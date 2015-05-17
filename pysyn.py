#!/usr/bin/env python
    
import ast
import copy
import inspect
import logging
import re
import sys
import z3
from os import path
import threading
    
logging.basicConfig(level = logging.WARN)
ABORT_TIMEOUT=10 ##!!! Set to higher level later on
WITH_HYPO = True

class FunctionLoader(object):
    """
    Offers functionality to load functions ('f' & 'f_inv') as ast trees
    """

    def __init__(self, p):
        assert path.isfile(p)

        self.path = p
        # they are used for lazy initialization
        self.source = None
        self.ast = None
        
    def has_f(self):
        p = self.get_ast()
        for node in p.body:
            if FunctionLoader.is_f(node):
                return True
        return False

    def has_template(self):
        p = self.get_ast()
        for node in p.body:
            if FunctionLoader.is_template(node):
                return True
        return False
   
    def get_source(self):
        if self.source == None:
            self.source = read_file_to_string(self.path)
        return self.source

    def get_ast(self):
        if self.ast == None:
            self.ast = ast.parse(self.get_source())
        return self.ast
   
    def get_f(self):
        p = self.get_ast()
        for node in p.body:
            if FunctionLoader.is_f(node):
                return node
  
    def get_template(self):
        assert self.has_template()
        p = self.get_ast()
        for node in p.body:
            if FunctionLoader.is_template(node):
                return node
                 
    @classmethod
    def is_f(cls, ast):
        return cls.is_function(ast, "f")
  
    @classmethod
    def is_template(cls, ast):
        return cls.is_function(ast, "f_inv")
   
    @classmethod
    def is_function(cls, ast, name):
        return type(ast).__name__ == "FunctionDef" and ast.name == name
    

class PathRaises(Exception):
    """
    Denotes that a path will raise an exception and is therefore no longer worth
    exploring.
    """
    pass


class GiveUp(Exception):
    """
    Denotes that the FunctionAnalyzer should give up analyzing a function.
    This may be raised if an irreversible path was found while analyzing
    for the 'syn' command, then it's no longer worth exploring other paths.
    """
    pass


class FunctionAnalyzer:
    
    """
    Creates Path objects for a function
    """
    
    def __init__(self, f):
        self.f = f
        
        # fetch parameters
        self.input = map(lambda p: z3.Int(p.id), f.args.args)
        self.input_names = set(map(lambda p: p.id, f.args.args))
        
        self.output = None

        self.solver = z3.Solver()
        # initialize argument constraint: x in [1000, -1000]
        self.solver.add(z3.And(*[p >= -1000 for p in self.input]))
        self.solver.add(z3.And(*[p <= 1000 for p in self.input]))

        # add parameters to store
        self.store = dict(zip(map(str, self.input), self.input)) 
        
        self.paths = []
        self.reachable = z3.sat
        self.return_size = -1

        self.is_irreversible = False
        self.migh_be_irreversible = False
        self.irreversible_path_constraints = []
    

    def analyze(self, give_up_on_irreversible_path = False):
        self.give_up_on_irreversible_path = give_up_on_irreversible_path

        try:
            self.explore_path(self.f.body)
        except GiveUp:
            pass


    def check_return_size(self, size):
        if self.return_size != -1 and self.return_size != size:
            raise Exception("Function is not part of the valid python subset due to unequal size of return tuples!")
        else:
            self.return_size = size
    

    def update_reachable(self):
        self.reachable = self.solver.check()
        
    
    def quick_check(self, *constraints):
        self.solver.push()
        self.solver.add(constraints)
        result = self.solver.check()
        self.solver.pop()
        return result


    def block(self, block):
        if len(block) > 0:
            self.statement(block[0], block[1:])
        else:
            if self.reachable == z3.sat:
                # path that doesn't end with a return statement!
                raise Exception("Function is not part of the valid python subset due to a missing return!")
            elif self.reachable == z3.unknown:
                # if we don't know whether a path is reachable
                # but it doesn't end with a return statement, we will assume
                # that it's not reachable, because it's clearly specified
                # that we're working with a python subset where every path
                # contains at least one return statement.
                pass
            else:
                assert(False)
    

    def statement(self, stmt, block):

        if type(stmt).__name__ == 'Return':
            self._return(stmt, block)

        elif type(stmt).__name__ == 'If':
            self._if(stmt, block)

        elif type(stmt).__name__ == 'Assign':
            self._assign(stmt, block)

        else:
            raise Exception('Invalid statement: ' + ast.dump(stmt))
    

    def _return(self, _return, block):
        
        expr = self.expression(_return.value)
        
        if isinstance(expr, tuple):
            self.check_return_size(len(expr))
            output = list(expr)
        else:
            self.check_return_size(1)
            output = [expr]
            
        relation = []
        
        # initialize output variables if necessary
        if self.output == None:
            
            self.output = []
            
            for i in xrange(len(output)):
                outname = "y" + str(i + 1)
            
                # avoid collisions with existing variables
                while outname in self.input_names:
                    outname = "__" + outname
    
                outvariable = z3.Int(outname)
                self.output.append(outvariable)
            
        for i in xrange(len(output)):
            relation.append(self.output[i] == output[i])
        
        path = Path(self.input, self.output, self.solver.assertions(), relation)
        self.paths.append(path)

    def _if(self, _if, block):
        
        # create check point
        self.solver.push()
        store = self.store.copy()
        reachable = self.reachable

        # fetch condition
        test = self.expression(_if.test)

        # handle true branch
        self.solver.add(test)
        self.update_reachable()
        
        # explore true branch
        if self.reachable == z3.sat or self.reachable == z3.unknown:
            self.explore_path(_if.body + block)
            
        # reset back to checkpoint
        self.solver.pop()
        self.store = store
        self.reachable = reachable

        # handle false branch
        self.solver.push()
        self.solver.add(z3.Not(test))
        self.update_reachable()
        
        # explore false branch
        if self.reachable == z3.sat or self.reachable == z3.unknown:

            if not _if.orelse:
                self.explore_path(block)
            else:
                self.explore_path(_if.orelse + block)
    
        self.solver.pop()
    

    def explore_path(self, block):
        try:
            self.block(block)
        except PathRaises:
            self.irreversible_path_constraints.append(list(self.solver.assertions()))
            if self.reachable == z3.sat:
                self.is_irreversible = True
                if self.give_up_on_irreversible_path:
                    raise GiveUp()
            elif self.reachable == z3.unknown:
                self.migh_be_irreversible = True
            else:
                assert(False)


    def _assign(self, assign, block):
        assert(len(assign.targets) == 1)  # Disallow a = b = c syntax
            
        target = self.assignable_expression(assign.targets[0])
        value = self.expression(assign.value)

        target_is_tuple = isinstance(target, tuple)
        value_is_tuple = isinstance(value, tuple)

        if target_is_tuple and value_is_tuple:
            if len(value) != len(target):
                # unequal size of tuples!
                raise PathRaises()

            for v, t in zip(value, target):
                self.store[t] = v
            
        elif not target_is_tuple and not target_is_tuple:
            self.store[target] = value

        else:
            # assignment of target and value have different types!
            raise PathRaises()
        
        self.block(block)
    
    
    def assignable_expression(self, expr):
        
        if type(expr).__name__ == 'Name':
            return expr.id

        if type(expr).__name__ == 'Tuple':
            return tuple(map(self.assignable_expression, expr.elts))
        
        raise Exception("Tried to assign to non-assignable expression! " + ast.dump(expr))
    
    
    def expression(self, expr):

        if type(expr).__name__ == 'Tuple':
            return tuple(map(self.expression, expr.elts))

        if type(expr).__name__ == 'Name':
            if self.store.has_key(expr.id):
                return self.store[expr.id]
            
            # variable doesn't exist, will raise a ValueError!
            raise PathRaises()

        if type(expr).__name__ == 'Num':
            return expr.n

        if type(expr).__name__ == 'BinOp':
            left = self.expression(expr.left)
            right = self.expression(expr.right)
            
            if type(expr.op).__name__ == 'Add':
                return left + right
            if type(expr.op).__name__ == 'Sub':
                return left - right
            if type(expr.op).__name__ == 'Mult':
                return left*right
            if type(expr.op).__name__ == 'Div':
                
                # for some reasons it seems that add with check seems to produce
                # better results than check with assumptions

                # can x be non-zero?
                non_zero = self.quick_check(right != 0)
                if non_zero == z3.sat or non_zero == z3.unknown:
                    
                    # check for division by zero
                    division_by_zero = self.quick_check(right == 0)
                    
                    # handle potential division by zero
                    if division_by_zero == z3.sat:
                        constraint = list(self.solver.assertions())
                        constraint.append(right == 0)
                        self.irreversible_path_constraints.append(constraint)
    
                        self.is_irreversible = True
                        if self.give_up_on_irreversible_path:
                            raise GiveUp()
    
                    elif division_by_zero == z3.unknown:
                        constraint = list(self.solver.assertions())
                        constraint.append(right == 0)
                        self.irreversible_path_constraints.append(constraint)
    
                        self.migh_be_irreversible = True
    
                    else:
                        # x can't be 0, so everything's good
                        pass

                    # continue with assumption that x != 0
                    self.solver.add(right != 0)
                    self.reachable = non_zero
                    
                    return left/right

                else:
                    # x can't be non-zero
                    raise PathRaises

        if type(expr).__name__ == 'UnaryOp':
            operand = self.expression(expr.operand)
            if type(expr.op).__name__ == 'Not':
                return z3.Not(operand)
            if type(expr.op).__name__ == 'USub':
                return -operand
            if type(expr.op).__name__ == 'UAdd':
                return operand

        if type(expr).__name__ == 'Compare':
            assert(len(expr.ops) == 1)  # Do not allow for x == y == 0 syntax
            assert(len(expr.comparators) == 1)
            
            left = self.expression(expr.left)
            right = self.expression(expr.comparators[0])

            op = expr.ops[0]
            if type(op).__name__ == 'Eq':
                return left == right
            if type(op).__name__ == 'NotEq':
                return left != right
            if type(op).__name__ == 'Gt':
                return left > right
            if type(op).__name__ == 'GtE':
                return left >= right
            if type(op).__name__ == 'Lt':
                return left < right
            if type(op).__name__ == 'LtE':
                return left <= right

        if type(expr).__name__ == 'BoolOp':
            operands = expr.values

            if type(expr.op).__name__ == 'And':
                real_operands = []
                for operand in operands:

                    operand = self.expression(operand)
                    real_operands.append(operand)

                    if self.quick_check(*real_operands) == z3.unsat:
                        # we could prove that the operands are false
                        # so therefore due to python's short-circuit and operator
                        # the remaining operands don't need to be evaluated
                        # anymore
                        break

                return z3.And(*real_operands)

            if type(expr.op).__name__ == 'Or':
                
                real_operands = []
                for operand in operands:

                    operand = self.expression(operand)
                    real_operands.append(operand)

                    if self.quick_check(z3.Not(z3.Or(*real_operands))) == z3.unsat:
                        # we could prove that the operands cannot be false
                        # thus the operands are always true
                        # so therefore with python's short-circuit or operator
                        # the remaining operands don't need to be evaluated
                        # anymore
                        break

                return z3.Or(*real_operands)

        raise Exception('Invalid expression: ' + ast.dump(expr))


class Path:
    
    """
    Entity class that represents a path
    """
    
    def __init__(self, input, output, constraints, relation):
        assert isinstance(input, list)
        assert isinstance(output, list)
        assert isinstance(relation, list)

        self.input = input
        self.output = output
        self.constraints = constraints
        self.relation = relation


class PathDataGenerator:
    
    """
    Generates input/output samples for a given path
    """
    
    def __init__(self, path):
        self.path = path

        self.solver = z3.Solver()
        self.solver.add(path.constraints)
        self.solver.add(path.relation)
        self.solver.push()
        
        self.stack_size = 0
    
    
    def another(self):
        
        sat = self.solver.check()
        if sat != z3.sat:
            return None
    
        model = self.solver.model()

        in_vector = [model[x].as_long() for x in self.path.input]
        out_vector = [model[y].as_long() for y in self.path.output]

        # make sure we don't generate the same sample twice
        self.solver.add(z3.Not(z3.And(*[ x == model[x] for x in self.path.input])))
        self.solver.add(z3.Not(z3.And(*[ y == model[y] for y in self.path.output])))

        self.solver.push()
        self.stack_size += 1
        
        return (in_vector, out_vector)

    
    def take(self, num):
        v = []
        for i in xrange(num):
            d = self.another()

            if d == None:
                return v

            v.append(d)

        return v
    
    def reset(self):
        while self.stack_size > 0:
            self.solver.pop()
            self.stack_size -= 1


class DiversePathDataGenerator:
    
    """
    Generates input/output samples with a strong emphasize on diversity
    """
    
    def __init__(self, path):
        self.path = path

        self.solver = z3.Solver()
        self.solver.add(path.constraints)
        self.solver.add(path.relation)
        self.solver.push()
        
    
    def generate_one(self):
        
        # try to find one
        if self.solver.check() != z3.sat:
            return None, None
        
        # extract solution
        model = self.solver.model()

        x_vec = [ model[x] for x in self.path.input ]
        y_vec = [ model[y] for y in self.path.output ]
        
        if None in x_vec or None in y_vec:
            return None, None
        
        x_vec = [ x.as_long() for x in x_vec]
        y_vec = [ y.as_long() for y in y_vec]
        
        return [y_vec, x_vec]
    
    
    def generate_k_for_dimension(self, k, d, avoid = []):
        
        assert(d < len(self.path.input))
        
        self.solver.push()

        # make sure we get a new value for the given dimension d
        self.solver.add([ self.path.input[d] != x[d] for x in avoid ])
        
        xs = []
        ys = []
        for i in xrange(k):
            y, x = self.generate_one()

            if x is None or y is None:
                break
            
            xs.append(x)
            ys.append(y)

            self.solver.add([ self.path.input[d] != x[d] ])
        
        self.solver.pop()
        
        return ys, xs
        
    
    def generate_k_per_dimension(self, k):
        
        xs = []
        ys = []

        for d in range(len(self.path.input)):
            _ys, _xs = self.generate_k_for_dimension(k, d, xs)

            xs += _xs
            ys += _ys
        
        return ys, xs
    
    
    def generate_k_different(self, k, avoid = []):
        
        self.solver.push()
        
        for x in avoid:
            self.solver.add(z3.Not(z3.And(*[ self.path.input[d] == x[d] for d in xrange(len(self.path.input)) ])))
            
        xs = []
        ys = []
        for i in xrange(k):

            y, x = self.generate_one()
            
            if x is None or y is None:
                break
            
            xs.append(x)
            ys.append(y)
            
            self.solver.add(z3.Not(z3.And(*[ self.path.input[d] == x[d] for d in xrange(len(self.path.input)) ])))
        
        self.solver.pop()
        
        return ys, xs
    

    def generate(self, k):
        
        ys, xs = self.generate_k_per_dimension(k)
        
        _ys, _xs = self.generate_k_different(k, xs)
        ys += _ys
        xs += _xs
        
        out = []
        
        for y, x in zip(ys, xs):
            out.append([y, x])
        
        return out


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


def compile_ast(f):
    """
    Compiles a function in ast form and returns it.
    
    Once returned the function can be called just like any other python function
    """
    assert(f.__class__.__name__ == "FunctionDef")

    ast.fix_missing_locations(f)
    m = ast.Module([f])
    compiled = compile(m, "<pysyn.compile_ast>", "exec")

    scope = {}
    exec compiled in scope
    return scope[f.name]


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
        vv.visit(find_function(self.tree, fname))
        
        # Pass the cond_context down to parent class so the instrumented ast tree will compile
        FunctionExecutor.__init__(self, self.tree, fname, {"cond_context":self})
        
        # choice is the bit pattern for the current branching path (ref id in wrap_call corresponds to bit number)
        #   Start with recognizable value --> need call to nextPath() to be ready for func calls
        #   nextPath() always increments choice, therefore walking through all branches
        self.choice = -1
        # where to stop iterating with next Path... set to the first unused bit (i.e. 1 bit above the biggest branch ref id)
        self.maxChoice = 1 << vv.refLength
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
        res = None
        try:
            res = FunctionExecutor.call(self, *args)
        finally:
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
            if node.right.__class__.__name__ != 'Call' or node.right.func.__class__.__name__ != 'Attribute' or node.right.func.attr != 'nonZero':
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
        if not node.func.__class__.__name__=='Attribute':
            return node
        
        if self.unknown_vars is not None and node.func.attr =='unknown_int':
            ref = node.args[0].n
            if not self.unknown_vars.has_key(ref):
                val=99999
                #raise Exception("trying to replace unknown_int with ref {0}. Solution not supplied: {1}".format(ref, self.unknown_vars))
                # Substitute with whatever value... Wasn't considered in the training data
            else:
                val = self.unknown_vars[ref]
            rv = ast.Num(n = val)
        elif self.unknown_choices is not None and node.func.attr =='unknown_choice': 
            ref = node.args[0].n
            if not self.unknown_choices.has_key(ref):
                sel=0
                #raise "trying to replace unknown_choice with ref {0}. Solution not supplied".format(ref)
                # Substitute with whatever value... Wasn't considered in the training data
            else:
                sel = self.unknown_choices[ref]
            rv = self.visit(node.args[sel +1])
        elif node.func.attr =='wrap_condition': 
            self.generic_visit(node)
            rv = node.args[1]
        elif node.func.attr =='nonZero': 
            self.generic_visit(node)
            rv = node.args[0]

        return rv


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
        #self.solver.set("max_steps",1000)
        #self.solver.set(solver2_timeout=1)
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

        def abortSolving():
            logging.debug("aborting solving")
            self.solver.ctx.interrupt()
                    
        timer=threading.Timer(ABORT_TIMEOUT,abortSolving)
        # this causes many threads to be started wich may cause severe slow downs
        timer.start()
        if not self.solver.check() == z3.sat:
            timer.cancel()
            logging.debug("solver stoped: {0}".format(self.solver.reason_unknown()))
            # Remove last condition... caued to fail.
            self.solver.pop()
            return None
            # And go for next one
            #break
            
        timer.cancel()
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
        
        self.outVars = []
            
        self.inVars = []
        for i in range(0, len(self.func.spec.args)):
            self.inVars.append(z3.Int('In'+str(i)))

    def inCond(self):
        cond = []
        for iv in self.inVars:
            cond.append(iv >= -1000)
            cond.append(iv <= 1000)
        return cond

    def matchVars(self, v, data):
        """
        Utility function to generate a z3 condition for a list
         * v: list of z3 variables (or other expressions)
         * data: list of data items to match with the correpsonding item in v
        return a z3 condition
        """
        cond = []
        if data is not None and not isinstance(data, (tuple,list)):
            data=(data,)
        if len(v) != len(data):
            # TODO: fix this for testcase 'solve' ./samples/zero_division/zero_div_guard.py
            logging.error("len(v) != len(data)!")

        for i in range(0, min(len(v), len(data))):
            cond.append(v[i] == data[i])
        return z3.And(*cond)
    
    def matchOut(self, data):
        """
        Create a z3 condition to match output variables 
        """
        
        # The number of elements returned may vary. --> increase output variable size on demand
        i = len(self.outVars)
        if data is not None and not isinstance(data, (tuple,list)):
            data=(data,)
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
            try:
                (res, path, extraCond) = self.func.callExt(*self.inVars)
            except:
                continue
            
            if not pathLog.addPath(path):
                # We encountered this path already... No need to add
                continue
            
            condRv = self.matchOut(res)
            condPath = path.pathCondition
            condProg += self.inCond()
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
            try:
                (res, path, extraCond) = self.func.callExt(*self.inVars)
            except:
                continue
                
            if res is None:
                continue
            if not pathLog.addPath(path):
                continue

            #condRv = self.matchOut(res)
            condPath = path.pathCondition

            logging.debug(condPath)
            #z3.Implies(condPath, condRv)

            varHack = []
            for iv in self.inVars:
                varHack.append(iv == z3.Int('tmp_'+str(iv)))
                
            varHack += self.inCond()
            condPath = z3.And(condPath, *varHack)

            solver.add(condPath)
            solver.add(extraCond)
            
            inData = solver.findSolution()
            if inData is None:
                # We didn't find any solution
                continue
            
            for i_in in range(0, len(self.inVars)):
                if inData is None:
                    break
                solver.reset()
                solver.add(condPath)
                
                i = 0
                while(i < k*len(self.inVars)):
                    # First only exclude one dimension, run through all dimensions
                    inData = solver.findSolutionAvoid(inData, [i_in])
                    if inData is None:
                        break
                    i += 1

            if inData is None:
                continue
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


    def reverseData(self, data):
        """
        Reverse input and output of the data set. Used when training the inverse of a function.
        """
        res = []
        for t in data:
            res.append([t[1], t[0]])
        return res;
    

    def genConditionsFrom(self, data, func = None):
        """
        Generate conditions from supplied data. Data has same format as return value of FunctionExecutor.genData
        NOTE: for training the inverse fkt, use reverseData() first to swap input/output of the training data
        """
        condProg = []
        if func is None:
            func = self.func

        pathLog = PathLog()
        func.resetPath()

        while func.nextPath():

            extraCondForced = []
            inVars = [ z3.Int('InSym_1_'+str(func.choice)+'_'+str(i)) for i in range(len(func.spec.args)) ]
            inVars2 = [ z3.Int('InSym_2_'+str(func.choice)+'_'+str(i)) for i in range(len(func.spec.args)) ]
            inVars3 = [ z3.Int('InSym_3_'+str(func.choice)+'_'+str(i)) for i in range(len(func.spec.args)) ]

            try:
                (res, path, extraCond) = func.callExt(*inVars)
                if not pathLog.addPath(path):
                    continue
                (res2, path2, extraCond2) = func.callExt(*inVars2)
                (res3, path3, extraCond3) = func.callExt(*inVars3)
            except:
                continue

            # 3 samples:
            #     1: sample on how to avoid not(extra cond) (e.g. Div/0)
            #     2: making sure that the path is reachable (avoid dead code)
            #     3: makins sure not(extra Cond) can be true at all 
            for i in range(len(extraCond)):
                cond = z3.And(z3.Not(path.pathCondition),z3.Not(extraCond[i]))
                pre = z3.And(path2.pathCondition,z3.Not(extraCond3[i]))
                # Only if we can reach the path and the extra cond could become an
                # issue...
                # Then we need to have a sample to guide the solver away.
                extraCondForced.append(z3.Implies(pre,cond))

            
            solver = z3.Solver()
            solver.add(*extraCondForced)
            if solver.check() == z3.sat:
                condProg += extraCondForced
        
        for t in data:
            func.resetPath()
            pathLog = PathLog()
            while func.nextPath():
                try:
                    (res, path, extraCond) = func.callExt(*(t[0]))
                except:
                    continue
                
                if isinstance(res,tuple) and len(res) != len(t[1]):
                    raise Exception("length of return value from func eval does not match training data length")
                
                if res is None:
                    continue
                
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

    def solveUnknowns(self, training_data, func = None):

        conds = self.genConditionsFrom(training_data, func)
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


    def filterHypos(self, training_data, hypos, k = 1):

        outHypo = []
        solution = []
        i = 0
        fd2 = []

        while i < len(training_data):
            fd2.append(training_data[i])
            i += k
        
        for hypo in hypos:
            try:
                ukv, ukc = self.solveUnknowns(training_data, hypo)
            except:
                # Any exception... treat as unsat hypo
                continue

            if ukv is not None:
                solution.append(ukv)
                outHypo.append(hypo)

        return (outHypo, solution)
    
    def solveHypos(self, training_data, hypos, k = 5):
        validHypos = hypos
        i = k
        while(i > 0):
            if len(validHypos) == 0:
                return ([], [])
            (validHypos, solutions) = self.filterHypos(training_data, validHypos, i)
            i = i >> 1
        return (validHypos, solutions)
    
    def templateHypos(self, hypos, sols):
        rv = []
        for i, sol in enumerate(sols):
            if sol is None:
                continue
            rv.append(FunctionExecutor( self.template(sol, None, hypos[i]), 'f_inv'))
        return rv


def solve_app(f_ast, ys):
    
    analyzer = FunctionAnalyzer(f_ast)
    analyzer.analyze()
    
    if len(analyzer.paths) == 0:
        # no valid paths -> all 'Unsat'
        
        return [['Unsat']]*len(ys)
    
    # prepare solver
    solver = z3.Solver()
    
    ors = []
    for path in analyzer.paths:
        ors.append(z3.And(
            z3.And(*path.constraints),
            z3.And(*path.relation)
            ))
    
    solver.add(z3.Or(ors))
    
    solver.push()
    
    num_constraints = len(list(solver.assertions()))
    
    xs = []
    for y in ys:

        if len(y) != len(analyzer.output):
            xs.append(['Unsat'])
            continue
        
        for i in xrange(len(y)):
            solver.add(analyzer.output[i] == y[i])
            
        if solver.check() == z3.sat:
            
            model = solver.model()
            
            x = [model[in_var].as_long() for in_var in analyzer.input]
            
            if None in x:
                xs.append(['Unsat'])
            else:
                xs.append(x)

        else:
        
            xs.append(['Unsat'])
        
        solver.pop()
        solver.push()
    
    return xs


def generate_training_data_for_synthesizer(paths, k):

    """
    Generates k input/output samples per path
    
    Format:
    
    [
    [[out1, out2, ... , outN], [in1, in2, ... , inN]]
    [[out1, out2, ... , outN], [in1, in2, ... , inN]]
    ...
    [[out1, out2, ... , outN], [in1, in2, ... , inN]]
    ]
    """

    data = []
    for path in paths:
        data += DiversePathDataGenerator(path).generate(k)
    
    return data


def syn_app(program):

    tree = ast.parse(program)

    setMulti = 32
    if WITH_HYPO:
        setMulti = 16
    
    analyzer = FunctionAnalyzer(find_function(tree, 'f'))
    analyzer.analyze(True)
    
    if analyzer.is_irreversible:
        return "Unsat"

    funcSynth = FuncSynthesizer(tree, 'f_inv')

    training_data = generate_training_data_for_synthesizer(analyzer.paths, setMulti*(len(find_function(tree, 'f').args.args) + 1))

    logging.debug(training_data)
    
    if WITH_HYPO:
        hypos = funcSynth.genHypotheses()
        (hypos, solutions) = funcSynth.solveHypos(training_data, hypos, 16)
        funcs = funcSynth.templateHypos(hypos, solutions)
        if len(funcs) == 0:
            return "Unsat"
        
        return ast_to_source(find_function(funcs[0].tree, 'f_inv'))
    
    else:
        unknown_vars, unknown_choices = funcSynth.solveUnknowns(training_data)
        if unknown_vars is None:
            return "Unsat"
        
        tr = funcSynth.template(unknown_vars, unknown_choices)
        return ast_to_source(find_function(tr, 'f_inv'))


def find_function(p, function_name):
    assert(type(p).__name__ == 'Module')
    for x in p.body:
        if type(x).__name__ == 'FunctionDef' and x.name == function_name:
            return x;
    raise Exception('Function %s not found' % (function_name))


def ast_to_source(ast, warn_unknown = True):
    return AstPrinter(ast, warn_unknown).get_source()

class AstPrinter:
    """
    Converts an ast node of a function to its textual representation (its source)
    
    If unknown_int() or unknown_choice(...) are encountered it'll print a warning
    if warn_unknown = True (default)
    """
    
    def __init__(self, f, warn_unknown = True):
        assert(type(f).__name__ == "FunctionDef")
        self.indentation = 0 
        self.f = f
    
    def get_source(self):
        out = "def " + self.f.name + "(" + ", ".join(map(self.expr_to_source, self.f.args.args)) + "):\n"
        self.indent()
        out += self.block_to_source(self.f.body)
        self.detent()
        return out

    def indent(self):
        self.indentation += 1
        
    def detent(self):
        self.indentation -= 1
    
    def emitln(self, line):
        return "    " *self.indentation + line + "\n"
    
    def block_to_source(self, block):
        return "".join(map(self.stmt_to_source, block))
    
    def stmt_to_source(self, stmt):
        
        if type(stmt).__name__ == 'Return':
            return self.emitln("return " + self.expr_to_source(stmt.value))

        if type(stmt).__name__ == 'If':

            out = self.emitln("if (" + self.expr_to_source(stmt.test) + "):")

            self.indent()
            out += self.block_to_source(stmt.body)
            self.detent()

            if stmt.orelse:
                out += self.emitln("else:")
    
                self.indent()
                out += self.block_to_source(stmt.orelse)
                self.detent()

            return out
        
        if type(stmt).__name__ == 'Assign':
            assert(len(stmt.targets) == 1)  # Disallow a = b = c syntax
            
            return self.emitln(self.expr_to_source(stmt.targets[0]) + " = " + self.expr_to_source(stmt.value))

        raise Exception('Unhandled statement: ' + ast.dump(stmt))
    
    def expr_to_source(self, expr):
        
        if type(expr).__name__ == 'Tuple':
            members = map(lambda expr: self.expr_to_source(expr), expr.elts)
            return ", ".join(members)

        if type(expr).__name__ == 'Name':
            return expr.id

        if type(expr).__name__ == 'Num':
            return str(expr.n)

        if type(expr).__name__ == 'BinOp':
            out = '(' + self.expr_to_source(expr.left) + ')'
            
            if type(expr.op).__name__ == 'Add':
                out += " + "
            if type(expr.op).__name__ == 'Sub':
                out += " - "
            if type(expr.op).__name__ == 'Mult':
                out += " * "
            if type(expr.op).__name__ == 'Div':
                out += " / "

            out += '('  + self.expr_to_source(expr.right) + ')'
            return out

        if type(expr).__name__ == 'UnaryOp':
            out = ""
            if type(expr.op).__name__ == 'Not':
                out = "not "
            if type(expr.op).__name__ == 'USub':
                out = "-"
                
            out += "(" + self.expr_to_source(expr.operand) + ")"
            return out

        if type(expr).__name__ == 'Compare':
            assert(len(expr.ops) == 1)  # Do not allow for x == y == 0 syntax
            assert(len(expr.comparators) == 1)

            out = "(" + self.expr_to_source(expr.left) + ")"

            op = expr.ops[0]
            if type(op).__name__ == 'Eq':
                out += " == "
            if type(op).__name__ == 'NotEq':
                out += " != "
            if type(op).__name__ == 'Gt':
                out += " > "
            if type(op).__name__ == 'GtE':
                out += " >= "
            if type(op).__name__ == 'Lt':
                out += " < "
            if type(op).__name__ == 'LtE':
                out += " <= "

            out += "(" + self.expr_to_source(expr.comparators[0]) + ")"
            return out

        if type(expr).__name__ == 'BoolOp':
            operands = map(lambda expr: "(" + self.expr_to_source(expr) + ")", expr.values)
            if type(expr.op).__name__ == 'And':
                return " and ".join(operands)
            if type(expr.op).__name__ == 'Or':
                return " or ".join(operands)

        raise Exception('Unhandled expression: ' + ast.dump(expr))


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
                run_block(stmt.body)
            else:
                run_block(stmt.orelse)
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
    
    def run_block(block):
        for stmt in block:
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
    run_block(f.body)
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


def load_vectors(p):
    """
    Loads the vectors from a file `p' into a list of lists
    
    see parse_vectors regarding the format of the list of lists
    """
    return parse_vectors(read_file_to_string(p))


def parse_vectors(s):
    """
    Parses the vectors from a string `s' into a list of lists
    
    a1 a2 a3 a4
    b1 b2 b3
    Unsat
    c1 c2 c3
    
    would become
    
    [
    [a1, a2, a3, a4],
    [b1, b2, b3],
    "Unsat",
    [c1, c2, c3]
    ]
    
    Where a1, a2, b1, c1 etc integers are
    """
    return [ map(lambda x: x if x == "Unsat" else int(x), vec.split(" ")) for vec in s.split("\n") if vec != '']


def print_usage():
    usage = """
Usage:
    %(cmd)s eval <python_file> <data_file>
    %(cmd)s solve <python_file> <data_file>
    %(cmd)s syn <python_file>
            """ % {"cmd":sys.argv[0]}
    print(usage)

def main_eval(source, data):
    eval_app(source, data)

def main_solve(source_file, test_file):
    out_vec = solve_app(FunctionLoader(source_file).get_f(), load_vectors(test_file))
    for out in out_vec:
        print " ".join(map(str, out))

def main_syn(source):
    print syn_app(source)

if __name__ == '__main__':
    if (len(sys.argv) == 1):
        print_usage()
        exit(1)
    if sys.argv[1] == 'eval':
        main_eval(read_file_to_string(sys.argv[2]), read_file_to_string(sys.argv[3]))
    elif sys.argv[1] == 'solve':
        main_solve(sys.argv[2], sys.argv[3])
    elif sys.argv[1] == 'syn':
        main_syn(read_file_to_string(sys.argv[2]))
    else:
        print "Unknown command %s" % (sys.argv[1])
        print_usage()
        exit(1)
    
