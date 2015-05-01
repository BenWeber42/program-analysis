#-------------------------------------------------------------------------------
# Name:        module1
# Purpose:
#
# Author:      Schultschik
#
# Created:     16.04.2015
# Copyright:   (c) Schultschik 2015
# Licence:     <your licence>
#-------------------------------------------------------------------------------


import z3
import re
#import ast
#import unparse
#from unparse import  * ## REMOVE
from astmanip import * ## REMOVE
from astexec import * ## REMOVE
from astexec import PathLog

class UnknownChoiceDesc():
    """
    Helper class to track unknown choice items
    Uses z3 variables:
      Sel_<refNo>_<choiceNo>          --> 0 or 1: if the argument choiceNo from the unknown_choice() call is used
      Var_<refNo>_<instanceCount>     --> z3 expr: returned from unknown_choice() to build conditions when running f_inv
      
    where
      refNo: Reference Id for the choice (as set by the InstrumentingVisitor)
      instanceCount: incremented each generateNewInstance() call so each function eval can have an independent value
                     (note: the function input may not be z3. accordingly the args of unknown_choice() are ints ,not z3 symbols)
    """
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

    @property
    def noChoices(self):
        return len(self.selection_vars);
    
    def generateNewInstance(self,args):
        """Generate new variable and conditions associated with the variable"""
        instCount=len(self._instance_vars)
        vr=z3.Int('Var'+str(self.ref)+'_'+str(instCount))
        self._instance_vars.append(vr)
        
        if len(args) != len(self.selection_vars):
            raise "arg length does not match prepared selection vars"
        
        for i in range(0,len(self.selection_vars)):
            self._selection_instance_conds.append(z3.Or(self.selection_vars[i]==0,vr==args[i]))
            
        return vr        

    @property
    def condition(self):
        """Returns the colllected conditions as list of z3 expression"""
        conds=self._selection_conds+self._selection_instance_conds
        return conds

class UnknownHandlingExecutor(InstrumentedExecutor):
    """Function executor that also supports unknown_int and unknown_choice in cond_context"""
    def __init__(self,astTree,fname='f'):    
        InstrumentedExecutor.__init__(self,astTree,fname)

        self.unknown_ints={}
        
        # Map of conditions per ref. Extended by each _choice run
        self.unknown_choices={}
        
        # List of all instance variables returned in _choice
        self.unknown_choices_vars=[]
        self.trainCnt=0

    def unknown_int(self,refNo):
        """Generates & returns a z3 variable with name Num_<refNo>"""
        if self.unknown_ints.has_key(refNo):
            return self.unknown_ints[refNo]
        
        v=z3.Int('Num'+str(refNo))
        self.unknown_ints[refNo]=v
        return v
    
    @property
    def choiceMaxStates(self):
        return self.visitor.unknown_choice_max
    
    def unknown_choice(self,refNo,*args):
        """generates conditions for choice and returns new var. See UnknownChoiceDesc for details"""
        if self.unknown_choices.has_key(refNo):
            desc=self.unknown_choices[refNo]
        else:
            desc=UnknownChoiceDesc(refNo, len(args))
            self.unknown_choices[refNo]=desc

        return desc.generateNewInstance(args)

    def choiceConditions(self):
        """Returns all conditions associated with all executions"""
        con=[]
        for x in self.unknown_choices.values():
            con+=x.condition
        return con

class ChoiceState:
    def __init__(self,maxStates):
        self._state={}
        self._order=[]
        self._max=maxStates
        for id in maxStates:
            self._state[id]=0
            self._order.append(id)
        self._initial=True
            
    @property
    def current(self):
        return self._state
    
    def __iter__(self):
        return self
    
    def next(self):
        if self._initial:
            self._initial=False
            return self._state
        
        for id in self._order:
            self._state[id]+=1
            if self._state[id]==self._max[id]:
                self._state[id]=0
            else:
                return self._state.copy()
        raise StopIteration


class FuncSynthesizer:
    """
    Function synthesizer
    Also adapts unknown_int and unknowon_choice in AST to train as template
    """
    
    def __init__(self,astTree,fname='f'):
        self.func=UnknownHandlingExecutor(astTree, fname)
        self.oFunc=FunctionExecutor(astTree, fname)
        

    def reverseData(self,data):
        """
        Reverse input and output of the data set. Used when taining the inverse of a function.
        """
        res=[]
        for t in data:
            res.append([t[1],t[0]])
        return res;
    
    def genConditionsFrom(self,data,func=None):
        """
        Generate conditions from supplied data. Data has same format as return value of FunctionExecutor.genData
        NOTE: for training the inverse fkt, use reverseData() first to swap input/outpu of the training data
        """
        condProg=[]
        if func is None:
            func=self.func
    
        for t in data:
            func.resetPath()
            pathLog=PathLog()
            while func.nextPath():
                (res,path,extraCond)=func.callExt(*(t[0]))
                if not pathLog.addPath(path):
                    continue
                
                condRv=[]
                if isinstance(res,tuple):
                    for i in range(0,len(res)):
                        condRv.append(res[i]==t[1][i])
                else:
                    condRv.append(res==t[1][0])
                condPath=path.pathCondition
                if z3.is_expr(condPath):                    
                    condProg.append(z3.Implies(condPath, z3.And(*condRv)))
                    condProg.append(z3.Implies(condPath, z3.And(*extraCond)))
                elif condPath:
                    condProg.append(z3.And(*condRv))
                    condProg.append(z3.And(*extraCond))
                    
            
        condProg+=func.choiceConditions()
        return condProg        
    
    def extractSolution(self,model):
        """
        Extract all choices/unknowns from the model
        """
        unknown_vars={}
        unknown_choices={}
        pat_num=re.compile('^Num(\d+)$')
        pat_sel=re.compile('^Sel(\d+)_(\d+)$')
        for v in model.decls():
            nmatch=pat_num.match(str(v))
            if nmatch:
                unknown_vars[int(nmatch.group(1))]=model[v].as_long()
                continue
            
            smatch=pat_sel.match(str(v))
            if smatch:
                if model[v].as_long()==0:
                    continue
                ref=int(smatch.group(1))
                sel=int(smatch.group(2))
                
                unknown_choices[ref]=sel
                
        return unknown_vars,unknown_choices

    def solveUnknowns(self,fd,func=None):
        conds=self.genConditionsFrom(fd,func)
        #print conds
        solver=z3.Solver()
        
        g=z3.Goal()
        g.add(*conds)
        #c2=g.simplify()        
        #solver.add(c2)
        solver.add(g)
    
        #print c2
        if not solver.check() == z3.sat:
            return (None,None)
        
        m=solver.model()
        return self.extractSolution(m)
        
    def template(self,unknown_vars, unknown_choices,func=None):
        if func is None:
            func=self.func
        v2=TemplateTransformer(unknown_vars, unknown_choices)
        tr2=copy.deepcopy(func.tree)
        v2.visit(tr2)
        return tr2

    def genHypoFkt(self,choiceState):
        tree=self.template(None, choiceState)
        ff=UnknownHandlingExecutor(tree, self.func.funcName)
        return ff;
            
    def genHypotheses(self):
        hypo=[]

        choiceState=ChoiceState(self.func.choiceMaxStates)
        for st in choiceState:
            hypo.append(self.genHypoFkt(st))

        return hypo
    
    def solveHypos(self,fd,hypos):
        solution=[]
        for hypo in hypos:
            ukv,ukc=self.solveUnknowns(fd, hypo)
            solution.append(ukv)
        return solution
    
    def templateHypos(self,hypos,sols):
        rv=[]
        for i,sol in enumerate(sols):
            if sol is None:
                continue
            rv.append(FunctionExecutor( self.template(sol, None,hypos[i]),'f_inv'))
        return rv
    