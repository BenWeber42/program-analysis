#!/usr/bin/env python
import ast
import copy
import cStringIO
import inspect
import logging
import os
import re
import sys
import z3

#
# Context class used when executing AST trees prepared by InstrumentingVisitor
#
# Provides instrumentation/wrapper functions injected in AST
# 
# Provides mechanism to iterate through all possible if trees by changing the
# result of the conditional in the wrapper (see nextPath())
#
# Use:
#    cc = SymExecContext(vv.refCnt)
#    sc = {"cond_context":cc}
#    sc2 = {}
#    exec(comp, sc, sc2)
#    rv = sc2['f'].__call__(*args)
#

class ExecutionPath:
    """
    Represents the conditions for one execution path.
    """
    
    def __init__(self):
        # List of conditions, each representing one branch decision
        self.cond = []
        # bit pattern of the current branch:
        #   reference ID of the if statement is the bit number (e.g. refId 2 --> bit 2 --> bitmask 4 (start bit count at 0)
        self.branchBits = 0
        #   To remember which branches we actually encountered, set corresponding bit
        #   --> Allows later on to sort out duplicate path settings (i.e. with bits set that were not encountered in exec
        self.maskBits = 0
    
    def addBranch(self, ref, selection, cond_in):
        """
        Adds a branch decision made at an if statement
         * ref: the reference id for the if
         * selection: the (forced) result of the condition (1 --> take if, 0 --> take else)
         * cond_in: the actual condition (usually z3 expression)
        """
        b = 1 <<ref;

        # In case we're evaluating mixed data, we may arrive here with only an int or bool value
        # --> Make sure to convert it into a boolean so z3 does not choke on it
        if not z3.is_expr(cond_in):
            cond_in = bool(cond_in)
        cond = cond_in

        # If we're not in the if branch, negate condition
        if not selection:
            cond = z3.Not(cond_in)
            
        self.cond.append(cond)
        
        if self.maskBits & b:
            raise "same branch encountered twice: {0}".format(ref)
        self.maskBits |= b
        self.branchBits |= (selection&1) <<ref
        
        
    def samePath(self, otherPath):
        # It's the same path if we went through the same if statements (maskBits)
        # ... and took the same branch for all these (branchBits)
        return otherPath.maskBits == self.maskBits and otherPath.branchBits&otherPath.maskBits == self.branchBits&self.maskBits
        
    @property
    def pathCondition(self):
        """Return the path condition as z3 expression"""
        if len(self.cond) == 0:
            return True
        else:
            return z3.And(*self.cond)

class PathLog:
    """Keeps track of paths already encountered"""
    
    def __init__(self):
        self.paths = []
        
    def addPath(self, path):
        """If not yet in paths, adds the path. Returns if the passed path has been added"""
        for p in self.paths:
            if p.samePath(path):
                return False
        self.paths.append(path)
        return True

class FunctionExecutor:
    """
    Compiles a given ast tree and provides functionality to execute an indicated function
    """
    
    def __init__(self, astTree, fname, global_vars = {}):
        """
         * ast tree : tree to parse (containing one or more func decls)
         * fname : function name to use in call()
         * global_vars: additional global variables the compilation
        """
        self.funcName = fname
        self.globalVars = global_vars
        self.tree = astTree
        
        #print ast.dump(tree.body[0])
        ast.fix_missing_locations(astTree)
        #unparse.Unparser(astTree)
        comp = compile(astTree, "<no >", "exec")
        self.localVars = {}
        exec(comp, global_vars, self.localVars)
        self.spec = inspect.getargspec(self.localVars[fname])
        self.func = self.localVars[fname]

    def call(self, *args):
        """Calls the function"""
        res = self.func.__call__(*args)
        return res
    
    def genData(self, inData):
        """
        Generates output data from input by calling the given function multiple times
         inData: list of list: e.g.: [[run1_arg1, run1_arg2], [run2_arg1, run2_arg2]]
        returns list of list of list:
           e.g. [
                   [[run1_arg1, run1_arg2], [run1_out1, run1_out2],
                   [[run2_arg1, run2_arg2], [run2_out1, run2_out2],
                ]
        Executions resulting in exceptions are skipped in the output
        """
        outData = []
        for dt in inData:
            try:
                res = self.call(*dt)
            except:
                # Maybe add logging here
                continue
            if isinstance(res, tuple):
                res = list(res)
            else:
                res = [res]
            outData.append([dt, res])

        return outData

class InstrumentedExecutor(FunctionExecutor):
    """
    Utility class for execution after instrumentation. To be bound to global variable "cond_context".
    Upon execution of the instrumented function forces execution along a predefined path and captures
    the conditions passed to the wrap_condition(). While 
    Can be switched to next path using nextPath()
    
    """
    def __init__(self, astTree, fname = 'f'):

        self.tree = copy.deepcopy(astTree)
        vv = InstrumentingVisitor()
        self.visitor = vv
        vv.visit(self.tree)
        
        # Pass the cond_context down to parent class so the instrumented ast tree will compile
        FunctionExecutor.__init__(self, self.tree, fname, {"cond_context":self})
        
        # choice is the bit pattern for the current branching path (ref id in wrap_call corresponds to bit number)
        #   Start with recognizable value --> need call to nextPath() to be ready for func calls
        #   nextPath() always increments choice, therefore walking through all branches
        self.choice = -1
        # where to stop iterating with next Path... set to the first unused bit (i.e. 1 bit above the biggest branch ref id)
        self.maxChoice = 1 <<vv.refLength
        # Only enable during call()
        self._currentPath = None
        self._extraCond = None

    def call(self, *args):
        """Executes a function with instrumentation, witout keeping the path setting. Only returns the result of the func"""
        if(self.choice == -1):
            raise "can only call after first use of nextPath()"
        self._currentPath = ExecutionPath()
        res = FunctionExecutor.call(self, *args)
        self._currentPath = None
        return res

    def callExt(self, *args):
        """Executes a function with instrumentation, returns return values and path object"""
        if(self.choice == -1):
            raise "can only call after first use of nextPath()"
        self._currentPath = ExecutionPath()
        self._extraCond = []
        res = FunctionExecutor.call(self, *args)
        pth = self._currentPath
        extraCond = self._extraCond
        self._currentPath = None
        self._extraCond = None
        return (res, pth, extraCond)

    def wrap_condition(self, ref, cond_in, outer):
        """Called from within the instrumented code, at each if condition"""
        rv = (self.choice >> ref) & 1
        self._currentPath.addBranch(ref, rv, cond_in)
        
        return rv;
    
    def nonZero(self, e):
        if(z3.is_expr(e)):
            self._extraCond.append(e != 0)
        elif e == 0:
            self._extraCond.append(False)
        return e
    
    def nextPath(self):
        """
        Advance to next path
        NOTE: as the path choice is iterating through all combinations of branching decisions,
              some combinations may be redundant as the changed branching decisions are not executed (outer if set differently)
              use PathLog.addPath() or ExecutionPath.samePath() to distinguish
        """
        self.choice = self.choice + 1
        return self.choice < self.maxChoice

    def resetPath(self):
        self.choice = -1

#
#
#   if x == 0:
#      ...
#   else:
#      y = 1/x
#
#
#   f(z3.Int('_X'))
# ....
#   if(x == 0):  #== z3.Expr('_X == 0')
#  -->
#   if(cond_context.wrap_condition(label, x == 0):
#
# ...
#
#        x = x + 1  #== z3.Expr('_X+1')
#             if cond_context.wrap_condition(label2, x >25):  #== z3.Expr('_X+1>25')
#
# expects global var cond_context: class with methods 
#    instrument(self, refNo, marker[[e.g. if endif else endelse]])
#    wrap_condition(self, refNo, condition, refToOuterIf)
#
#  Use  instance.visit(astTree) to start adding instrumentation
#
class InstrumentingVisitor(ast.NodeTransformer):
    """
    AST Node transformer that inserts instrumentation into the tree.
     * All instrumentation is implemented as method call on variable "cond_context". 
     * If conditions are wrapped by "cond_context.wrap_condition(<<ReferenceId>>, <<original condition>>, <<OuterIfId>>)
       * ReferenceId: Each wrapped condition is associated with an id (counting upward from 0).
       * original condition: AST tree of the original condition
       * OuterIfID: In case of nested ifs: The ReferenceID of the next ancestor IF in the tree
     * Additionally transforms unknown_int and unknown_choice into a method call and adds reference IDs:
       --> cond_context.unknown_choice(<<ReferenceId>>, <<original args>>)
       --> cond_context.unknown_int(<<ReferenceId>>
       
    TODOS:
    * Currently same reference ID or even same class for unknowns and if instrumentation --> separate
    """
    
    def __init__(self):
        self.refCnt = 0
        self.refCntUnknowns = 0
        self.outer = -1
        self._unknowns = {}
        self.unknown_choice_max = {}

    ctx_var = ast.Name(id = 'cond_context', ctx = ast.Load())
    
    @property
    def refLength(self):
        """Contains the last ReferenceId used for IFs +1 (array length semantics)"""
        return self.refCnt
    
    @property
    def unknowns(self):
        """returns a map unknownId --> corresponding Call node in the AST tree"""
        return self._unknowns
    
    def gen_wrap_call(self, t):
        """Generate the condition wrapper call. t is the AST expression tree for the conditional"""
        func = ast.Attribute(value = InstrumentingVisitor.ctx_var, attr='wrap_condition', ctx = ast.Load())
        return ast.Call(func = func, args = [ast.Num(n = self.refCnt), t, ast.Num(n=self.outer)], keywords=[])
        
    def generic_visit(self, node):
        """ 
           Override the visitor's generic method to find If conditions and Calls in the tree
           TODO: better override visit_If and visit_Call instead.
        """
        #print ast.dump(node)
        # keep track of nested IFs
        prevOuter = self.outer

        if node.__class__.__name__ == 'BinOp' and node.op.__class__.__name__ == "Div":
            if node.right.func.__class__.__name__ != 'Attribute' or node.right.func.attr != 'nonZero':
                fname = ast.Attribute(value = InstrumentingVisitor.ctx_var, attr="nonZero", ctx = ast.Load())
                node.right = ast.Call(func = fname, args=[node.right], keywords=[])
        elif node.__class__.__name__ == 'Call' and node.func.__class__.__name__ == 'Name':
            if node.func.id == 'unknown_int':
                node.func = ast.Attribute(value = InstrumentingVisitor.ctx_var, attr="unknown_int", ctx= ast.Load())
                node.args.insert(0, ast.Num(n = self.refCntUnknowns))
                self._unknowns[self.refCntUnknowns] = node
                self.refCntUnknowns += 1
            elif node.func.id == 'unknown_choice':
                node.func = ast.Attribute(value = InstrumentingVisitor.ctx_var, attr="unknown_choice", ctx= ast.Load())
                maxch = len(node.args)
                node.args.insert(0, ast.Num(n = self.refCntUnknowns))
                self._unknowns[self.refCntUnknowns] = node
                self.unknown_choice_max[self.refCntUnknowns] = maxch
                self.refCntUnknowns += 1
        elif node.__class__.__name__ == 'If' :
            #print ast.dump(node.test)
            t = node.test
            node.test = self.gen_wrap_call(t)
            self.outer = self.refCnt
            self.refCnt = self.refCnt + 1

        #print node.__class__.__name__
        # Go through all children... original method would do this already.
        for c in ast.iter_child_nodes(node):
            self.visit(c)
            
        # keep track of nested IFs
        self.outer = prevOuter
        return node


class TemplateTransformer(ast.NodeTransformer):
    """
    Replaces unknown_int and unknown_choice with the supplied values
    Requires that the visited AST tree has been instrumented (using InstrumentingVisitor) as the
    replacements are matched by ReferenceId.
    """
    
    def __init__(self, unknown_vars, unknown_choices):
        """
        Constructor. Requires two maps to replace unknown_ints and unknown_choices:
         * unknown_ints: ReferenceId -> integer literal to replace with
         * unknwon_choice: ReferenceId -> argument of the function to substitute the call with
           e.g. cond_context.unknown_choice(4, v0, v1, v2) ( {4:1} ) --> replace by "v1" in AST
        """
        self.unknown_vars = unknown_vars
        self.unknown_choices = unknown_choices

    def visit_Call(self, node):
        """
        called from generic_visitor during visit for all calls. only reacts on unknown_... methods
        """
        rv = node
        if self.unknown_vars is not None and node.func.attr =='unknown_int':
            ref = node.args[0].n
            if not self.unknown_vars.has_key(ref):
                raise Exception("trying to replace unknown_int with ref {0}. Solution not supplied: {1}".format(ref, self.unknown_vars))
            val = self.unknown_vars[ref]
            rv = ast.Num(n = val)
        elif self.unknown_choices is not None and node.func.attr =='unknown_choice': 
            ref = node.args[0].n
            if not self.unknown_choices.has_key(ref):
                raise "trying to replace unknown_choice with ref {0}. Solution not supplied".format(ref)
            sel = self.unknown_choices[ref]
            rv = node.args[sel +1]
        elif node.func.attr =='wrap_condition': 
            self.generic_visit(node)
            rv = node.args[1]
        elif node.func.attr =='nonZero': 
            self.generic_visit(node)
            rv = node.args[0]

        return rv


# Test Cases: 
#    Input unrelate output
#    Assembly/disassemly by switch/case
#    Result dep on single in-var --> rest undefined
#    Div 0
#    Overflow



class ResultIteratingSolver:
    """
    Wrapper around z3 solver that allows trying additional conditions. z3 solver backtracking undoes the condition
    on failure.
    The class furthermore keeps track of all found results and excludes these from future search by adding a z3 condition    
    """
    
    def __init__(self, vars, baseCond = []):
        """
         vars: list of z3 variables/expressions
         baseCond: base conditions always present
        """
        self.solver = z3.Solver()
        self.previousSolutionConds = []
        self.baseCond = baseCond
        self.solver.add(*baseCond)
        self.vars = vars
        self.results = []
    
    
    def reset(self):
        """Reset conditions, but add base conditions and exclude previous solutions"""
        self.solver.reset()
        self.solver.add(*self.baseCond)
        self.solver.add(*self.previousSolutionConds)

    def add(self, *conds):
        """normal add for z3.Solver"""
        self.solver.add(*conds)
        
    def genAvoidCondition(self, inData, forVars = None):
        """
        Generate condition to avoid results for certain variable dimensions
         * inData: list, e.g. previous solution
         * forVars: indices in variable list, rsp. inData.
        returns condition: inData[i] != vars[i] (i in forVars) 
        """
        if forVars is None:
            forVars = range(0, len(self.vars))
        if len(inData) != len(self.vars):
            raise "length of data ({0}) and length of input vars ({1}) do not match".format(len(inData), len(self.vars))
        return z3.And(*[ self.vars[i] != inData[i] for i in forVars ])

    def findSolutionAvoid(self, inData, forVars = None):
        """Find solution avoiding results in certain variable dimensions, see genAvoidCondition"""
        cond = self.genAvoidCondition(inData, forVars)
        return self.findSolution(cond)

    def findSolution(self, *newConds):
        """
        try to find solution. If successful, add exclusion condition, add to result and return data. 
        Else return None, leave solver in original state
        """
        self.solver.push()
        self.solver.add(*newConds);
        if not self.solver.check() == z3.sat:
            # Remove last condition... caued to fail.
            self.solver.pop()
            return None
            # And go for next one
            #break
            
        m = self.solver.model()
        res = [m[x].as_long() for x in self.vars]
        self.previousSolutionConds.append(self.genAvoidCondition(res))
        self.results.append(res)
        return res

    



class FuncAnalyzer:
    """
    Function analyzer/synthesizer
    """
    
    def __init__(self, astTree, fname ='f'):
        self.func = InstrumentedExecutor(astTree, fname)
        self.oFunc = FunctionExecutor(astTree, fname)
        
        self.outVars = []
            
        self.inVars = []
        for i in range(0, len(self.func.spec.args)):
            self.inVars.append(z3.Int('In'+str(i)))

    def matchVars(self, v, data):
        """
        Utility function to generate a z3 condition for a list
         * v: list of z3 variables (or other expressions)
         * data: list of data items to match with the correpsonding item in v
        return a z3 condition
        """
        cond = []
        for i in range(0, len(v)):
            cond.append(v[i] == data[i])
        return z3.And(*cond)
    
    def matchOut(self, data):
        """
        Create a z3 condition to match output variables 
        """
        
        # The number of elements returned may vary. --> increase output variable size on demand
        i = len(self.outVars)
        while i < len(data):
            self.outVars.append(z3.Int('Out'+str(i)))
            i = i +1
        return self.matchVars(self.outVars, data)

    def calcForward(self):
        """
        Generate z3 conditions between input and output for all branch paths of given func.
        Uses z3 variables in inVars and outVars.
        """

        pathLog = PathLog()
        condProg = []
    
        self.func.resetPath()
        while self.func.nextPath():
            #print self.func
            (res, path, extraCond) = self.func.callExt(*self.inVars)
            if not pathLog.addPath(path):
                # We encountered this path already... No need to add
                continue
            
            condRv = self.matchOut(res)
            condPath = path.pathCondition
            condProg.append(z3.Implies(condPath, condRv))
            condProg.append(z3.Implies(condPath, z3.And( *extraCond)))
            
        return condProg

    def genTrainer(self, data):
        
        condProg = []
    
        while self.context.nextPath():
            #print self.func
            for t in data:
                self.context.resetExec()
                res = self.func.__call__( *(t[1]))
                condRv = []
                if isinstance(res, tuple):
                    for i in range(0, len(res)):
                        condRv.append(res[i] == t[0][i])
                else:
                    condRv.append(res == t[0][0])
                condPath = self.pathCondition()
                condProg.append(z3.Implies(condPath, z3.And( *condRv)))
            
        condProg += self.choiceRunConditions()
        condProg += self.globalUnknownsCondition()
        return condProg        

    def genInput(self, k):
        """
        Generate input data for given function based on branching conditions.
        Find k*(len(inVars)+1) solutions within each branch. Avoids duplicate solutions between branches
        Branches that show no (or no more) solutions are skipped.
        """
    
        solver = ResultIteratingSolver(self.inVars)
        
        pathLog = PathLog()
        while self.func.nextPath():
            solver.reset()
            (res, path, extraCond) = self.func.callExt(*self.inVars)
            if not pathLog.addPath(path):
                continue

            #condRv = self.matchOut(res)
            condPath = path.pathCondition
            #print condPath
            #z3.Implies(condPath, condRv)

            varHack = []
            for iv in self.inVars:
                varHack.append(iv == z3.Int('tmp_'+str(iv)))
                
            condPath = z3.And(condPath, *varHack)

            solver.add(condPath)
            solver.add(extraCond)
            
            inData = solver.findSolution()
            if inData is None:
                # We didn't find any solution
                continue
            
            for i_in in range(0, len(self.inVars)):
                solver.reset()
                solver.add(condPath)
                
                i = 0
                while(i < k*len(self.inVars)):
                    # First only exclude one dimension, run through all dimensions
                    inData = solver.findSolutionAvoid(inData, [i_in])
                    if inData is None:
                        break
                    i += 1

            # Now again, across all vars, find whatever other solutions
            while(i < k *len(self.inVars)):
                inData = solver.findSolution(inData)
                if inData is None:
                    break
                i += 1
            

        return solver.results

class UnknownChoiceDesc():
    """
    Helper class to track unknown choice items
    Uses z3 variables:
      Sel_<refNo>_<choiceNo>          --> 0 or 1: if the argument choiceNo from the unknown_choice() call is used
      Var_<refNo>_<instanceCount>     --> z3 expr: returned from unknown_choice() to build conditions when running f_inv
      
    where
      refNo: Reference Id for the choice (as set by the InstrumentingVisitor)
      instanceCount: incremented each generateNewInstance() call so each function eval can have an independent value
                     (note: the function input may not be z3. accordingly the args of unknown_choice() are ints , not z3 symbols)
    """
    def __init__(self, refNo, choiceCnt):
        self.ref = refNo
        self.selection_vars = []
        self._selection_conds = []
        self._selection_instance_conds = []
        self._instance_vars = []
        sm = 0
        for i in range(0, choiceCnt):
            v = z3.Int('Sel'+str(refNo) +'_'+str(i))
            self.selection_vars.append(v)
            self._selection_conds.append(z3.Or(v == 0, v == 1))
            sm = sm +v
        self._selection_conds.append(sm == 1)

    @property
    def noChoices(self):
        return len(self.selection_vars);
    
    def generateNewInstance(self, args):
        """Generate new variable and conditions associated with the variable"""
        instCount = len(self._instance_vars)
        vr = z3.Int('Var'+str(self.ref)+'_'+str(instCount))
        self._instance_vars.append(vr)
        
        if len(args) != len(self.selection_vars):
            raise "arg length does not match prepared selection vars"
        
        for i in range(0, len(self.selection_vars)):
            self._selection_instance_conds.append(z3.Or(self.selection_vars[i] == 0, vr == args[i]))
            
        return vr        

    @property
    def condition(self):
        """Returns the colllected conditions as list of z3 expression"""
        conds = self._selection_conds+self._selection_instance_conds
        return conds

class UnknownHandlingExecutor(InstrumentedExecutor):
    """Function executor that also supports unknown_int and unknown_choice in cond_context"""
    def __init__(self, astTree, fname = 'f'):    
        InstrumentedExecutor.__init__(self, astTree, fname)

        self.unknown_ints = {}
        
        # Map of conditions per ref. Extended by each _choice run
        self.unknown_choices = {}
        
        # List of all instance variables returned in _choice
        self.unknown_choices_vars = []
        self.trainCnt = 0

    def unknown_int(self, refNo):
        """Generates & returns a z3 variable with name Num_<refNo >"""
        if self.unknown_ints.has_key(refNo):
            return self.unknown_ints[refNo]
        
        v = z3.Int('Num'+str(refNo))
        self.unknown_ints[refNo] = v
        return v
    
    @property
    def choiceMaxStates(self):
        return self.visitor.unknown_choice_max
    
    def unknown_choice(self, refNo, *args):
        """generates conditions for choice and returns new var. See UnknownChoiceDesc for details"""
        if self.unknown_choices.has_key(refNo):
            desc = self.unknown_choices[refNo]
        else:
            desc = UnknownChoiceDesc(refNo, len(args))
            self.unknown_choices[refNo] = desc

        return desc.generateNewInstance(args)

    def choiceConditions(self):
        """Returns all conditions associated with all executions"""
        con = []
        for x in self.unknown_choices.values():
            con += x.condition
        return con

class ChoiceState:
    def __init__(self, maxStates):
        self._state = {}
        self._order = []
        self._max = maxStates
        for id in maxStates:
            self._state[id] = 0
            self._order.append(id)
        self._initial = True
            
    @property
    def current(self):
        return self._state
    
    def __iter__(self):
        return self
    
    def next(self):
        if self._initial:
            self._initial = False
            return self._state
        
        for id in self._order:
            self._state[id] += 1
            if self._state[id] == self._max[id]:
                self._state[id] = 0
            else:
                return self._state.copy()
        raise StopIteration


class FuncSynthesizer:
    """
    Function synthesizer
    Also adapts unknown_int and unknowon_choice in AST to train as template
    """
    
    def __init__(self, astTree, fname = 'f'):
        self.func = UnknownHandlingExecutor(astTree, fname)
        self.oFunc = FunctionExecutor(astTree, fname)
        

    def reverseData(self, data):
        """
        Reverse input and output of the data set. Used when taining the inverse of a function.
        """
        res = []
        for t in data:
            res.append([t[1], t[0]])
        return res;
    
    def genConditionsFrom(self, data, func = None):
        """
        Generate conditions from supplied data. Data has same format as return value of FunctionExecutor.genData
        NOTE: for training the inverse fkt, use reverseData() first to swap input/outpu of the training data
        """
        condProg = []
        if func is None:
            func = self.func
    
        for t in data:
            func.resetPath()
            pathLog = PathLog()
            while func.nextPath():
                (res, path, extraCond) = func.callExt(*(t[0]))
                if not pathLog.addPath(path):
                    continue
                
                condRv = []
                if isinstance(res, tuple):
                    for i in range(0, len(res)):
                        condRv.append(res[i] == t[1][i])
                else:
                    condRv.append(res == t[1][0])
                condPath = path.pathCondition
                if z3.is_expr(condPath):                    
                    condProg.append(z3.Implies(condPath, z3.And(*condRv)))
                    condProg.append(z3.Implies(condPath, z3.And(*extraCond)))
                elif condPath:
                    condProg.append(z3.And(*condRv))
                    condProg.append(z3.And(*extraCond))
                    
            
        condProg += func.choiceConditions()
        return condProg        
    
    def extractSolution(self, model):
        """
        Extract all choices/unknowns from the model
        """
        unknown_vars = {}
        unknown_choices = {}
        pat_num = re.compile('^Num(\d+)$')
        pat_sel = re.compile('^Sel(\d+)_(\d+)$')
        for v in model.decls():
            nmatch = pat_num.match(str(v))
            if nmatch:
                unknown_vars[int(nmatch.group(1))] = model[v].as_long()
                continue
            
            smatch = pat_sel.match(str(v))
            if smatch:
                if model[v].as_long() == 0:
                    continue
                ref = int(smatch.group(1))
                sel = int(smatch.group(2))
                
                unknown_choices[ref] = sel
                
        return unknown_vars, unknown_choices

    def solveUnknowns(self, fd, func = None):
        conds = self.genConditionsFrom(fd, func)
        #print conds
        solver = z3.Solver()
        
        g = z3.Goal()
        g.add( *conds)
        #c2 = g.simplify()        
        #solver.add(c2)
        solver.add(g)
    
        #print c2
        if not solver.check() == z3.sat:
            return (None, None)
        
        m = solver.model()
        return self.extractSolution(m)
        
    def template(self, unknown_vars, unknown_choices, func = None):
        if func is None:
            func = self.func
        v2 = TemplateTransformer(unknown_vars, unknown_choices)
        tr2 = copy.deepcopy(func.tree)
        v2.visit(tr2)
        return tr2

    def genHypoFkt(self, choiceState):
        tree = self.template(None, choiceState)
        ff = UnknownHandlingExecutor(tree, self.func.funcName)
        return ff;
            
    def genHypotheses(self):
        hypo = []

        choiceState = ChoiceState(self.func.choiceMaxStates)
        for st in choiceState:
            hypo.append(self.genHypoFkt(st))

        return hypo


    def filterHypos(self, fd, hypos, k = 1):
        outHypo = []
        solution = []
        i = 0
        fd2 = []
        while i <len(hypos):
            fd2.append(fd[i])
            i += k
        
        for hypo in hypos:
            ukv, ukc = self.solveUnknowns(fd, hypo)
            if(ukv is not None):
                solution.append(ukv)
                outHypo.append(hypo)
        return (outHypo, solution)
    
    def solveHypos(self, fd, hypos, k = 5):
        validHypos = hypos
        i = k
        while(i > 0):
            if len(validHypos) == 0:
                return ([], [])
            (validHypos, solutions) = self.filterHypos(fd, validHypos, i)
            i = i >> 1
        return (validHypos, solutions)
    
    def templateHypos(self, hypos, sols):
        rv = []
        for i, sol in enumerate(sols):
            if sol is None:
                continue
            rv.append(FunctionExecutor( self.template(sol, None, hypos[i]), 'f_inv'))
        return rv

WITH_HYPO = True
logging.basicConfig(level = logging.WARN)

def solve_app(program, tests):
	p = ast.parse(program)
	logging.debug("AST Tree of read file:\n"+ast.dump(p))
	f = find_function(p, 'f')
	
	fa = FuncAnalyzer(p)
	
	
	solver = z3.Solver()
	conds = fa.calcForward()
	for test in tests.split('\n'):
		if len(test) == 0:
			continue		
		outdata = [ int(x) for x in test.split(' ') ]
		solver.reset()
		solver.add(*conds)
		solver.add(fa.matchOut(outdata))

		logging.info("Conditions for Solver:\n"+str(solver.assertions()))
		if(solver.check() == z3.sat):
			m = solver.model()
			logging.info("Model :\n"+str(m))
			#varNames = [str(x) for x in fa.inVars]
			vals = [m[x] for x in fa.inVars]
			print(' '.join([ str(x) for x in vals]))
		else:
			print "Unsat\n"


def syn_app(program):
	tree = ast.parse(program)
	
	funcAnalyzer = FuncAnalyzer(tree, 'f')
	origfunc = FunctionExecutor(tree, 'f')
	setMulti = 32
	if WITH_HYPO:
		setMulti = 16
	trainingData = funcAnalyzer.genInput(setMulti)
	trainingData = origfunc.genData(trainingData)
	funcSynth = FuncSynthesizer(tree, 'f_inv')
	trainingData = funcSynth.reverseData(trainingData)
	#print trainingData
	
	if WITH_HYPO:
		hypos = funcSynth.genHypotheses()
		(hypos, solutions) = funcSynth.solveHypos(trainingData, hypos, 16)
		funcs = funcSynth.templateHypos(hypos, solutions)
		if(len(funcs) == 0):
			print "Unsat"
			return 1
		
		Unparser(find_function(funcs[0].tree, 'f_inv'))
	
	else:
		unknown_vars, unknown_choices = funcSynth.solveUnknowns(trainingData)
		if unknown_vars is None:
			print "Unsat"
			return 1
		
		tr = funcSynth.template(unknown_vars, unknown_choices)
		Unparser(find_function(tr, 'f_inv'))

def find_function(p, function_name):
	assert(type(p).__name__ == 'Module')
	for x in p.body:
		if type(x).__name__ == 'FunctionDef' and x.name == function_name:
			return x;
	raise Exception('Function %s not found' % (function_name))

def eval_f(f, indata):
	assert(type(f).__name__ == 'FunctionDef')
	current = {}
	# print(ast.dump(f))
	eval_f.returned = False
	eval_f.return_val = []
	
	def run_expr(expr):
		if type(expr).__name__ == 'Tuple':
			r = []
			for el in expr.elts:
				r.append(run_expr(el))
			return tuple(r)
		if type(expr).__name__ == 'Name':
			return current[expr.id]
		if type(expr).__name__ == 'Num':
			return expr.n
		if type(expr).__name__ == 'BinOp':
			if type(expr.op).__name__ == 'Add':
				return run_expr(expr.left) + run_expr(expr.right)
			if type(expr.op).__name__ == 'Sub':
				return run_expr(expr.left) - run_expr(expr.right)			
			if type(expr.op).__name__ == 'Mult':
				return run_expr(expr.left) * run_expr(expr.right)
			if type(expr.op).__name__ == 'Div':
				return run_expr(expr.left) / run_expr(expr.right)
		if type(expr).__name__ == 'UnaryOp':
			if type(expr.op).__name__ == 'Not':
				return not run_expr(expr.operand)
			if type(expr.op).__name__ == 'USub':
				return -run_expr(expr.operand)
		if type(expr).__name__ == 'Compare':
			assert(len(expr.ops) == 1)  # Do not allow for x == y == 0 syntax
			assert(len(expr.comparators) == 1)
			e1 = run_expr(expr.left)
			op = expr.ops[0]
			e2 = run_expr(expr.comparators[0])
			if type(op).__name__ == 'Eq':
				return e1 == e2
			if type(op).__name__ == 'NotEq':
				return e1 != e2			
			if type(op).__name__ == 'Gt':
				return e1 > e2
			if type(op).__name__ == 'GtE':
				return e1 >= e2
			if type(op).__name__ == 'Lt':
				return e1 < e2
			if type(op).__name__ == 'LtE':
				return e1 <= e2
		if type(expr).__name__ == 'BoolOp':
			if type(expr.op).__name__ == 'And':
				r = True
				for v in expr.values:
					r = r and run_expr(v)
					if not r:
						break
				return r
			if type(expr.op).__name__ == 'Or':
				r = False
				for v in expr.values:
					r = r or run_expr(v)
					if r:
						break
				return r			
		raise Exception('Unhandled expression: ' + ast.dump(expr))
	
	def run_stmt(stmt):
		if type(stmt).__name__ == 'Return':
			eval_f.returned = True
			eval_f.return_val = run_expr(stmt.value)
			return
		if type(stmt).__name__ == 'If':
			cond = run_expr(stmt.test)
			if cond:
				run_body(stmt.body)
			else:
				run_body(stmt.orelse)
			return
		if type(stmt).__name__ == 'Assign':
			assert(len(stmt.targets) == 1)  # Disallow a = b = c syntax
			lhs = stmt.targets[0]
			rhs = run_expr(stmt.value)
			if type(lhs).__name__ == 'Tuple':
				assert(type(rhs).__name__ == 'tuple')
				assert(len(rhs) == len(lhs.elts))
				for el_index in range(len(lhs.elts)):
					el = lhs.elts[el_index]
					assert(type(el).__name__ == 'Name')
					current[el.id] = rhs[el_index]
				return
			if type(lhs).__name__ == 'Name':
				current[lhs.id] = rhs
				return
		raise Exception('Unhandled statement: ' + ast.dump(stmt))
	
	def run_body(body):
		for stmt in body:
			run_stmt(stmt)
			if eval_f.returned:
				return
	
	# Set initial current:
	assert(len(indata) == len(f.args.args))
	arg_index = 0
	for arg in f.args.args:
		assert(type(arg).__name__ == 'Name')
		current[arg.id] = indata[arg_index]
		arg_index = arg_index + 1
	# print(current)
	run_body(f.body)
	assert(eval_f.returned)
	if type(eval_f.return_val).__name__ == 'tuple':
		return eval_f.return_val
	return tuple([eval_f.return_val])


def eval_app(program, tests):
	p = ast.parse(program)
	# print(ast.dump(p))
	f = find_function(p, 'f')
	for test in tests.split('\n'):
		if len(test) == 0:
			continue		
		indata = [ int(x) for x in test.split(' ') ]
		print(' '.join([ str(x) for x in eval_f(f, indata) ]))

def read_file_to_string(filename):
	f = open(filename, 'rt')
	s = f.read()
	f.close()
	return s

def print_usage():
	usage = """
Usage:
	%(cmd)s eval <python_file> <data_file>
	%(cmd)s solve <python_file> <data_file>
	%(cmd)s syn <python_file>
			""" % {"cmd":sys.argv[0]}
	print(usage)

# Large float and imaginary literals get turned into infinities in the AST.
# We unparse those infinities to INFSTR.
INFSTR = "1e" + repr(sys.float_info.max_10_exp + 1)

def interleave(inter, f, seq):
    """Call f on each item in seq, calling inter() in between.
    """
    seq = iter(seq)
    try:
        f(next(seq))
    except StopIteration:
        pass
    else:
        for x in seq:
            inter()
            f(x)

class Unparser:
    """Methods in this class recursively traverse an AST and
    output source code for the abstract syntax; original formatting
    is disregarded. """

    def __init__(self, tree, file = sys.stdout):
        """Unparser(tree, file = sys.stdout) -> None.
         Print the source for tree to file."""
        self.f = file
        self.future_imports = []
        self._indent = 0
        self.dispatch(tree)
        self.f.write("")
        self.f.flush()

    def fill(self, text = ""):
        "Indent a piece of text, according to the current indentation level"
        self.f.write("\n"+"    "*self._indent + text)

    def write(self, text):
        "Append a piece of text to the current line."
        self.f.write(text)

    def enter(self):
        "Print ':', and increase the indentation."
        self.write(":")
        self._indent += 1

    def leave(self):
        "Decrease the indentation level."
        self._indent -= 1

    def dispatch(self, tree):
        "Dispatcher function, dispatching tree type T to method _T."
        if isinstance(tree, list):
            for t in tree:
                self.dispatch(t)
            return
        meth = getattr(self, "_"+tree.__class__.__name__)
        meth(tree)


    ############### Unparsing methods ######################
    # There should be one method per concrete grammar type #
    # Constructors should be grouped by sum type. Ideally, #
    # this would follow the order in the grammar, but      #
    # currently doesn't.                                   #
    ########################################################

    def _Module(self, tree):
        for stmt in tree.body:
            self.dispatch(stmt)

    # stmt
    def _Expr(self, tree):
        self.fill()
        self.dispatch(tree.value)

    def _Import(self, t):
        self.fill("import ")
        interleave(lambda: self.write(", "), self.dispatch, t.names)

    def _ImportFrom(self, t):
        # A from __future__ import may affect unparsing, so record it.
        if t.module and t.module == '__future__':
            self.future_imports.extend(n.name for n in t.names)

        self.fill("from ")
        self.write("." * t.level)
        if t.module:
            self.write(t.module)
        self.write(" import ")
        interleave(lambda: self.write(", "), self.dispatch, t.names)

    def _Assign(self, t):
        self.fill()
        for target in t.targets:
            self.dispatch(target)
            self.write(" = ")
        self.dispatch(t.value)

    def _AugAssign(self, t):
        self.fill()
        self.dispatch(t.target)
        self.write(" "+self.binop[t.op.__class__.__name__]+"= ")
        self.dispatch(t.value)

    def _Return(self, t):
        self.fill("return")
        if t.value:
            self.write(" ")
            self.dispatch(t.value)

    def _Pass(self, t):
        self.fill("pass")

    def _Break(self, t):
        self.fill("break")

    def _Continue(self, t):
        self.fill("continue")

    def _Delete(self, t):
        self.fill("del ")
        interleave(lambda: self.write(", "), self.dispatch, t.targets)

    def _Assert(self, t):
        self.fill("assert ")
        self.dispatch(t.test)
        if t.msg:
            self.write(", ")
            self.dispatch(t.msg)

    def _Exec(self, t):
        self.fill("exec ")
        self.dispatch(t.body)
        if t.globals:
            self.write(" in ")
            self.dispatch(t.globals)
        if t.locals:
            self.write(", ")
            self.dispatch(t.locals)

    def _Print(self, t):
        self.fill("print ")
        do_comma = False
        if t.dest:
            self.write(">>")
            self.dispatch(t.dest)
            do_comma = True
        for e in t.values:
            if do_comma:self.write(", ")
            else:do_comma = True
            self.dispatch(e)
        if not t.nl:
            self.write(",")

    def _Global(self, t):
        self.fill("global ")
        interleave(lambda: self.write(", "), self.write, t.names)

    def _Yield(self, t):
        self.write("(")
        self.write("yield")
        if t.value:
            self.write(" ")
            self.dispatch(t.value)
        self.write(")")

    def _Raise(self, t):
        self.fill('raise ')
        if t.type:
            self.dispatch(t.type)
        if t.inst:
            self.write(", ")
            self.dispatch(t.inst)
        if t.tback:
            self.write(", ")
            self.dispatch(t.tback)

    def _TryExcept(self, t):
        self.fill("try")
        self.enter()
        self.dispatch(t.body)
        self.leave()

        for ex in t.handlers:
            self.dispatch(ex)
        if t.orelse:
            self.fill("else")
            self.enter()
            self.dispatch(t.orelse)
            self.leave()

    def _TryFinally(self, t):
        if len(t.body) == 1 and isinstance(t.body[0], ast.TryExcept):
            # try-except-finally
            self.dispatch(t.body)
        else:
            self.fill("try")
            self.enter()
            self.dispatch(t.body)
            self.leave()

        self.fill("finally")
        self.enter()
        self.dispatch(t.finalbody)
        self.leave()

    def _ExceptHandler(self, t):
        self.fill("except")
        if t.type:
            self.write(" ")
            self.dispatch(t.type)
        if t.name:
            self.write(" as ")
            self.dispatch(t.name)
        self.enter()
        self.dispatch(t.body)
        self.leave()

    def _ClassDef(self, t):
        self.write("\n")
        for deco in t.decorator_list:
            self.fill("@")
            self.dispatch(deco)
        self.fill("class "+t.name)
        if t.bases:
            self.write("(")
            for a in t.bases:
                self.dispatch(a)
                self.write(", ")
            self.write(")")
        self.enter()
        self.dispatch(t.body)
        self.leave()

    def _FunctionDef(self, t):
        self.write("\n")
        for deco in t.decorator_list:
            self.fill("@")
            self.dispatch(deco)
        self.fill("def "+t.name + "(")
        self.dispatch(t.args)
        self.write(")")
        self.enter()
        self.dispatch(t.body)
        self.leave()

    def _For(self, t):
        self.fill("for ")
        self.dispatch(t.target)
        self.write(" in ")
        self.dispatch(t.iter)
        self.enter()
        self.dispatch(t.body)
        self.leave()
        if t.orelse:
            self.fill("else")
            self.enter()
            self.dispatch(t.orelse)
            self.leave()

    def _If(self, t):
        self.fill("if ")
        self.dispatch(t.test)
        self.enter()
        self.dispatch(t.body)
        self.leave()
        # collapse nested ifs into equivalent elifs.
        while (t.orelse and len(t.orelse) == 1 and
               isinstance(t.orelse[0], ast.If)):
            t = t.orelse[0]
            self.fill("elif ")
            self.dispatch(t.test)
            self.enter()
            self.dispatch(t.body)
            self.leave()
        # final else
        if t.orelse:
            self.fill("else")
            self.enter()
            self.dispatch(t.orelse)
            self.leave()

    def _While(self, t):
        self.fill("while ")
        self.dispatch(t.test)
        self.enter()
        self.dispatch(t.body)
        self.leave()
        if t.orelse:
            self.fill("else")
            self.enter()
            self.dispatch(t.orelse)
            self.leave()

    def _With(self, t):
        self.fill("with ")
        self.dispatch(t.context_expr)
        if t.optional_vars:
            self.write(" as ")
            self.dispatch(t.optional_vars)
        self.enter()
        self.dispatch(t.body)
        self.leave()

    # expr
    def _Str(self, tree):
        # if from __future__ import unicode_literals is in effect,
        # then we want to output string literals using a 'b' prefix
        # and unicode literals with no prefix.
        if "unicode_literals" not in self.future_imports:
            self.write(repr(tree.s))
        elif isinstance(tree.s, str):
            self.write("b" + repr(tree.s))
        elif isinstance(tree.s, unicode):
            self.write(repr(tree.s).lstrip("u"))
        else:
            assert False, "shouldn't get here"

    def _Name(self, t):
        self.write(t.id)

    def _Repr(self, t):
        self.write("`")
        self.dispatch(t.value)
        self.write("`")

    def _Num(self, t):
        repr_n = repr(t.n)
        # Parenthesize negative numbers, to avoid turning (-1)**2 into -1**2.
        if repr_n.startswith("-"):
            self.write("(")
        # Substitute overflowing decimal literal for AST infinities.
        self.write(repr_n.replace("inf", INFSTR))
        if repr_n.startswith("-"):
            self.write(")")

    def _List(self, t):
        self.write("[")
        interleave(lambda: self.write(", "), self.dispatch, t.elts)
        self.write("]")

    def _ListComp(self, t):
        self.write("[")
        self.dispatch(t.elt)
        for gen in t.generators:
            self.dispatch(gen)
        self.write("]")

    def _GeneratorExp(self, t):
        self.write("(")
        self.dispatch(t.elt)
        for gen in t.generators:
            self.dispatch(gen)
        self.write(")")

    def _SetComp(self, t):
        self.write("{")
        self.dispatch(t.elt)
        for gen in t.generators:
            self.dispatch(gen)
        self.write("}")

    def _DictComp(self, t):
        self.write("{")
        self.dispatch(t.key)
        self.write(": ")
        self.dispatch(t.value)
        for gen in t.generators:
            self.dispatch(gen)
        self.write("}")

    def _comprehension(self, t):
        self.write(" for ")
        self.dispatch(t.target)
        self.write(" in ")
        self.dispatch(t.iter)
        for if_clause in t.ifs:
            self.write(" if ")
            self.dispatch(if_clause)

    def _IfExp(self, t):
        self.write("(")
        self.dispatch(t.body)
        self.write(" if ")
        self.dispatch(t.test)
        self.write(" else ")
        self.dispatch(t.orelse)
        self.write(")")

    def _Set(self, t):
        assert(t.elts) # should be at least one element
        self.write("{")
        interleave(lambda: self.write(", "), self.dispatch, t.elts)
        self.write("}")

    def _Dict(self, t):
        self.write("{")
        def write_pair(pair):
            (k, v) = pair
            self.dispatch(k)
            self.write(": ")
            self.dispatch(v)
        interleave(lambda: self.write(", "), write_pair, zip(t.keys, t.values))
        self.write("}")

    def _Tuple(self, t):
        self.write("(")
        if len(t.elts) == 1:
            (elt, ) = t.elts
            self.dispatch(elt)
            self.write(",")
        else:
            interleave(lambda: self.write(", "), self.dispatch, t.elts)
        self.write(")")

    unop = {"Invert":"~", "Not": "not", "UAdd":"+", "USub":"-"}
    def _UnaryOp(self, t):
        self.write("(")
        self.write(self.unop[t.op.__class__.__name__])
        self.write(" ")
        # If we're applying unary minus to a number, parenthesize the number.
        # This is necessary: -2147483648 is different from -(2147483648) on
        # a 32-bit machine (the first is an int, the second a long), and
        # -7j is different from -(7j).  (The first has real part 0.0, the second
        # has real part -0.0.)
        if isinstance(t.op, ast.USub) and isinstance(t.operand, ast.Num):
            self.write("(")
            self.dispatch(t.operand)
            self.write(")")
        else:
            self.dispatch(t.operand)
        self.write(")")

    binop = { "Add":"+", "Sub":"-", "Mult":"*", "Div":"/", "Mod":"%",
                    "LShift":"<<", "RShift":">>", "BitOr":"|", "BitXor":"^", "BitAnd":"&",
                    "FloorDiv":"//", "Pow": "**"}
    def _BinOp(self, t):
        self.write("(")
        self.dispatch(t.left)
        self.write(" " + self.binop[t.op.__class__.__name__] + " ")
        self.dispatch(t.right)
        self.write(")")

    cmpops = {"Eq":"==", "NotEq":"!=", "Lt":"<", "LtE":"<=", "Gt":">", "GtE":">=",
                        "Is":"is", "IsNot":"is not", "In":"in", "NotIn":"not in"}
    def _Compare(self, t):
        self.write("(")
        self.dispatch(t.left)
        for o, e in zip(t.ops, t.comparators):
            self.write(" " + self.cmpops[o.__class__.__name__] + " ")
            self.dispatch(e)
        self.write(")")

    boolops = {ast.And: 'and', ast.Or: 'or'}
    def _BoolOp(self, t):
        self.write("(")
        s = " %s " % self.boolops[t.op.__class__]
        interleave(lambda: self.write(s), self.dispatch, t.values)
        self.write(")")

    def _Attribute(self, t):
        self.dispatch(t.value)
        # Special case: 3.__abs__() is a syntax error, so if t.value
        # is an integer literal then we need to either parenthesize
        # it or add an extra space to get 3 .__abs__().
        if isinstance(t.value, ast.Num) and isinstance(t.value.n, int):
            self.write(" ")
        self.write(".")
        self.write(t.attr)

    def _Call(self, t):
        self.dispatch(t.func)
        self.write("(")
        comma = False
        for e in t.args:
            if comma: self.write(", ")
            else: comma = True
            self.dispatch(e)
        for e in t.keywords:
            if comma: self.write(", ")
            else: comma = True
            self.dispatch(e)
            #if t.starargs:
            #    if comma: self.write(", ")
            #    else: comma = True
            #    self.write("*")
            #    self.dispatch(t.starargs)
        #if t.kwargs:
        #    if comma: self.write(", ")
        #    else: comma = True
        #    self.write("**")
        #    self.dispatch(t.kwargs)
        self.write(")")

    def _Subscript(self, t):
        self.dispatch(t.value)
        self.write("[")
        self.dispatch(t.slice)
        self.write("]")

    # slice
    def _Ellipsis(self, t):
        self.write("...")

    def _Index(self, t):
        self.dispatch(t.value)

    def _Slice(self, t):
        if t.lower:
            self.dispatch(t.lower)
        self.write(":")
        if t.upper:
            self.dispatch(t.upper)
        if t.step:
            self.write(":")
            self.dispatch(t.step)

    def _ExtSlice(self, t):
        interleave(lambda: self.write(', '), self.dispatch, t.dims)

    # others
    def _arguments(self, t):
        first = True
        # normal arguments
        defaults = [None] * (len(t.args) - len(t.defaults)) + t.defaults
        for a, d in zip(t.args, defaults):
            if first:first = False
            else: self.write(", ")
            self.dispatch(a),
            if d:
                self.write("=")
                self.dispatch(d)

        # varargs
        if t.vararg:
            if first:first = False
            else: self.write(", ")
            self.write("*")
            self.write(t.vararg)

        # kwargs
        if t.kwarg:
            if first:first = False
            else: self.write(", ")
            self.write("**"+t.kwarg)

    def _keyword(self, t):
        self.write(t.arg)
        self.write("=")
        self.dispatch(t.value)

    def _Lambda(self, t):
        self.write("(")
        self.write("lambda ")
        self.dispatch(t.args)
        self.write(": ")
        self.dispatch(t.body)
        self.write(")")

    def _alias(self, t):
        self.write(t.name)
        if t.asname:
            self.write(" as "+t.asname)

if __name__ == '__main__':
	if (len(sys.argv) == 1):
		print_usage()
		exit(1)
	if sys.argv[1] == 'eval':
		eval_app(read_file_to_string(sys.argv[2]), read_file_to_string(sys.argv[3]))
	elif sys.argv[1] == 'solve':
		solve_app(read_file_to_string(sys.argv[2]), read_file_to_string(sys.argv[3]))
	elif sys.argv[1] == 'syn':
		syn_app(read_file_to_string(sys.argv[2]))
	else:
		print "Unknown command %s" % (sys.argv[1])
		print_usage()
		exit(1)
	