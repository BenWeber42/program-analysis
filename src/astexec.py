#-------------------------------------------------------------------------------
# Name:        astmanip
# Purpose:
#
# Author:      Schultschik
#
# Created:     16.04.2015
# Copyright:   (c) Schultschik 2015
# Licence:     <your licence>
#-------------------------------------------------------------------------------


import z3
import ast
from astmanip import InstrumentingVisitor
import inspect
import copy

#
# Context class used when executing AST trees prepared by InstrumentingVisitor
#
# Provides instrumentation/wrapper functions injected in AST
# 
# Provides mechanism to iterate through all possible if trees by changing the
# result of the conditional in the wrapper (see nextPath())
#
# Use:
#    cc=SymExecContext(vv.refCnt)
#    sc={"cond_context":cc}
#    sc2={}
#    exec(comp,sc,sc2)
#    rv=sc2['f'].__call__(*args)
#

class ExecutionPath:
    """
    Represents the conditions for one execution path.
    """
    
    def __init__(self):
        # List of conditions, each representing one branch decision
        self.cond=[]
        # bit pattern of the current branch:
        #   reference ID of the if statement is the bit number (e.g. refId 2 --> bit 2 --> bitmask 4 (start bit count at 0)
        self.branchBits=0
        #   To remember which branches we actually encountered, set corresponding bit
        #   --> Allows later on to sort out duplicate path settings (i.e. with bits set that were not encountered in exec
        self.maskBits=0
    
    def addBranch(self,ref,selection,cond_in):
        """
        Adds a branch decision made at an if statement
         * ref: the reference id for the if
         * selection: the (forced) result of the condition (1 --> take if, 0 --> take else)
         * cond_in: the actual condition (usually z3 expression)
        """
        b=1<<ref;

        # In case we're evaluating mixed data, we may arrive here with only an int or bool value
        # --> Make sure to convert it into a boolean so z3 does not choke on it
        if not z3.is_expr(cond_in):
            cond_in=bool(cond_in)
        cond=cond_in

        # If we're not in the if branch, negate condition
        if not selection:
            cond=z3.Not(cond_in)
            
        self.cond.append(cond)
        
        if self.maskBits & b:
            raise "same branch encountered twice: {0}".format(ref)
        self.maskBits|=b
        self.branchBits|=(selection&1)<<ref
        
        
    def samePath(self,otherPath):
        # It's the same path if we went through the same if statements (maskBits)
        # ... and took the same branch for all these (branchBits)
        return otherPath.maskBits==self.maskBits and otherPath.branchBits&otherPath.maskBits == self.branchBits&self.maskBits
        
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
        self.paths=[]
        
    def addPath(self,path):
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
    
    def __init__(self,astTree,fname, global_vars={}):
        """
         * ast tree : tree to parse (containing one or more func decls)
         * fname : function name to use in call()
         * global_vars: additional global variables the compilation
        """
        self.funcName=fname
        self.globalVars=global_vars
        
        #print ast.dump(tree.body[0])
        ast.fix_missing_locations(astTree)
        #unparse.Unparser(astTree)
        comp=compile(astTree, "<no>", "exec")
        self.localVars={}
        exec(comp,global_vars,self.localVars)
        self.spec=inspect.getargspec(self.localVars[fname])
        self.func=self.localVars[fname]

    def call(self,*args):
        """Calls the function"""
        res=self.func.__call__(*args)
        return res
    
    def genData(self,inData):
        """
        Generates output data from input by calling the given function multiple times
         inData: list of list: e.g.: [[run1_arg1,run1_arg2],[run2_arg1,run2_arg2]]
        returns list of list of list:
           e.g. [
                   [[run1_arg1,run1_arg2],[run1_out1,run1_out2],
                   [[run2_arg1,run2_arg2],[run2_out1,run2_out2],
                ]
        Executions resulting in exceptions are skipped in the output
        """
        outData=[]
        for dt in inData:
            try:
                res=self.call(*dt)
            except:
                # Maybe add logging here
                continue
            if isinstance(res, tuple):
                res=list(res)
            else:
                res=[res]
            outData.append([dt,res])

        return outData

class InstrumentedExecutor(FunctionExecutor):
    """
    Utility class for execution after instrumentation. To be bound to global variable "cond_context".
    Upon execution of the instrumented function forces execution along a predefined path and captures
    the conditions passed to the wrap_condition(). While 
    Can be switched to next path using nextPath()
    
    """
    def __init__(self,astTree,fname='f'):

        self.tree=copy.deepcopy(astTree)
        vv=InstrumentingVisitor()
        vv.visit(self.tree)
        
        # Pass the cond_context down to parent class so the instrumented ast tree will compile
        FunctionExecutor.__init__(self,self.tree,fname,{"cond_context":self})
        
        # choice is the bit pattern for the current branching path (ref id in wrap_call corresponds to bit number)
        #   Start with recognizable value --> need call to nextPath() to be ready for func calls
        #   nextPath() always increments choice, therefore walking through all branches
        self.choice=-1
        # where to stop iterating with next Path... set to the first unused bit (i.e. 1 bit above the biggest branch ref id)
        self.maxChoice=1<<vv.refLength
        # Only enable during call()
        self._currentPath=None

    def call(self,*args):
        """Executes a function with instrumentation, witout keeping the path setting. Only returns the result of the func"""
        if(self.choice==-1):
            raise "can only call after first use of nextPath()"
        self._currentPath=ExecutionPath()
        res=FunctionExecutor.call(self,*args)
        self._currentPath=None
        return res

    def callExt(self,*args):
        """Executes a function with instrumentation, returns return values and path object"""
        if(self.choice==-1):
            raise "can only call after first use of nextPath()"
        self._currentPath=ExecutionPath()
        res=FunctionExecutor.call(self,*args)
        pth=self._currentPath
        self._currentPath=None
        return (res,pth)

    def wrap_condition(self,ref,cond_in,outer):
        """Called from within the instrumented code, at each if condition"""
        rv=(self.choice>>ref)&1
        self._currentPath.addBranch(ref, rv, cond_in)
        
        return rv;
    
    def nextPath(self):
        """
        Advance to next path
        NOTE: as the path choice is iterating through all combinations of branching decisions,
              some combinations may be redundant as the changed branching decisions are not executed (outer if set differently)
              use PathLog.addPath() or ExecutionPath.samePath() to distinguish
        """
        self.choice=self.choice+1
        return self.choice<self.maxChoice

    def resetPath(self):
        self.choice=-1

