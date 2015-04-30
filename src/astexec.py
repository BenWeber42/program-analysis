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
        self.cond=[]
        self.branchBits=0
        self.maskBits=0
    
    def addBranch(self,ref,selection,cond_in):
        b=1<<ref;

        if not z3.is_expr(cond_in):
            cond_in=bool(cond_in)
        cond=cond_in

        if not selection:
            cond=z3.Not(cond_in)
            
        self.cond.append(cond)
        if self.maskBits & b:
            raise "same branch encountered twice: {0}".format(ref)
        self.maskBits|=b
        self.branchBits|=b
        
        
    def samePath(self,otherPath):
        return otherPath.branchBits&otherPath.maskBits == self.branchBits&self.maskBits
    
    @property
    def pathCondition(self):
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
    def __init__(self,astTree,fname, global_vars={}):
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
        res=self.func.__call__(*args)
        return res

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
        vv.visit(astTree)
        
        FunctionExecutor.__init__(self,astTree,fname,{"cond_context":self.context})
        
        self.choice=-1
        self.maxChoice=1<<vv.refLength()
        self._currentPath=None

    def call(self,*args):
        self._currentPath=ExecutionPath()
        res=FunctionExecutor.call(self,*args)
        self._currentPath=None
        return res

    def callExt(self,*args):
        self._currentPath=ExecutionPath()
        res=FunctionExecutor.call(self,*args)
        pth=self._currentPath
        self._currentPath=None
        return (res,pth)

    def wrap_condition(self,ref,cond_in,outer):
        rv=(self.choice>>ref)&1
        self._currentPath.addBranch(ref, rv, cond_in)
        
        return rv;
    
    def nextPath(self):
        self.choice=self.choice+1
        return self.choice<self.maxChoice


class UnknownChoiceDesc():
    def __init__(self,refNo,choiceCnt):
        self.ref=refNo
        self.selection_vars=[]
        self._selection_conds=[]
        self._selection_instance_conds=[]
        self._instance_vars=[]
        sm=0
        for i in range(0,choiceCnt):
            v=z3.Int('Sel'+str(refNo)+'_'+str(i))
            self.selection_vars.append(v)
            self._selection_conds.append(z3.Or(v==0,v==1))
            sm=sm+v
            self._selection_conds.append(sm==1)

    def generateNewInstance(self,args):
        instCount=len(self._instance_vars)
        vr=z3.Int('Var'+str(self.ref)+'_'+str(instCount))
        self._instance_vars.append(vr)
        
        if len(args) != len(self.selection_vars):
            raise "arg length does not match prepared selection vars"
        
        for i in range(0,len(self.selection_vars)):
            self.selection_instance_conds.append(z3.Implies(self.selection_vars[i]==1,vr==args[i]))
            
        return vr        

    @property
    def condition(self):
        """Returns the colllected conditions as list of z3 expression"""
        conds=self._selection_conds+self._selection_instance_conds
        return conds

class UnknownHandlingExecutor(InstrumentedExecutor):
    def __init__(self,astTree,fname='f'):    
        InstrumentedExecutor.__init__(self,astTree,fname)

        self.unknown_ints={}
        
        # Map of conditions per ref. Extended by each _choice run
        self.unknown_choices={}
        
        # List of all instance variables returned in _choice
        self.unknown_choices_vars=[]
        self.trainCnt=0

    def unknown_int(self,refNo):
        if self.unknown_ints.has_key(refNo):
            return self.unknown_ints[refNo]
        
        v=z3.Int('Num'+str(refNo))
        self.unknown_ints[refNo]=v
        return v
    
    def unknown_choice(self,refNo,*args):
        
        if self.unknown_choices.has_key(refNo):
            desc=self.unknown_choices[refNo]
        else:
            selv=UnknownChoiceDesc(refNo, len(args))
            self.unknown_choices[refNo]=desc

        return selv.generateNewInstance(args)

    def choiceConditions(self):
        """Returns all conditions associated with all executions"""
        con=[]
        for x in self.unknown_choices:
            con+=x.condition()
        if
        return con
