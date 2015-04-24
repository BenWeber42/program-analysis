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
import inspect
#import ast
#import unparse
import copy
#from unparse import  * ## REMOVE
from astmanip import * ## REMOVE

# Test Cases: 
#    Input unrelate output
#    Assembly/disassemly by switch/case
#    Result dep on single in-var --> rest undefined
#    Div 0
#    Overflow

class FuncAnalyzer:
    def __init__(self,astTree,fname='f'):
        self.funcName=fname
        self.tree=copy.deepcopy(astTree)
        self.oFunc=None
        
        self.tree_copy=copy.deepcopy(astTree)

        vv=InstrumentingVisitor()
        vv.visit(astTree)
        #print ast.dump(tree.body[0])
        ast.fix_missing_locations(astTree)
        #unparse.Unparser(astTree)
        comp=compile(astTree, "<no>", "exec")
        self.context=SymExecContext(vv.refCnt)
        sc={"cond_context":self.context}
        sc2={}
        exec(comp,sc,sc2)
        spec=inspect.getargspec(sc2[fname])
        self.func=sc2[fname]
        
        self.outVars=[]
            
        self.inVars=[]
        for i in range(0,len(spec.args)):
            self.inVars.append(z3.Int('In'+str(i)))

    def orig_f(self):
        if self.oFunc==None:
            comp=compile(self.tree_copy, "<no>", "exec")
            sc={}
            sc2={}
            exec(comp,sc,sc2)
            self.oFunc=sc2[self.funcName]
        return self.oFunc

    def template(self,unknown_vars, unknown_choices):
        v2=TemplateTransformer(unknown_vars, unknown_choices)
        tr2=copy.deepcopy(self.tree)
        v2.visit(tr2)
        return tr2

    def pathCondition(self):
        if len(self.context.cond.values())==0:
            return 1==1;
        return z3.And(*(self.context.cond.values()))

    def choiceRunConditions(self):
        con=[]
        for x in self.context.unknown_choices.values():
            con+=x[1]
        return con

    def globalUnknownsCondition(self):
        con=[]
        for x in self.context.unknown_choices_vars.values():
            con+=x[1]
        return con

    def matchVars(self,v,data):
        cond=[]
        for i in range(0,len(v)):
            cond.append(v[i]==data[i])
        return z3.And(*cond)
    
    def matchOut(self,data):
        i=len(self.outVars)
        while i<len(data):
            self.outVars.append(z3.Int('Out'+str(i)))
            i=i+1
        return self.matchVars(self.outVars, data)

    def calcForward(self):
        
        condProg=[]
    
        while self.context.nextPath():
            #print self.func
            res=self.func.__call__(*self.inVars)
            condRv=self.matchOut(res)
            condPath=self.pathCondition()
            condProg.append(z3.Implies(condPath, condRv))
            
        return condProg

    def genTrainer(self,data):
        
        condProg=[]
    
        while self.context.nextPath():
            #print self.func
            for t in data:
                self.context.resetExec()
                res=self.func.__call__(*(t[1]))
                condRv=[]
                if isinstance(res,tuple):
                    for i in range(0,len(res)):
                        condRv.append(res[i]==t[0][i])
                else:
                    condRv.append(res==t[0][0])
                condPath=self.pathCondition()
                condProg.append(z3.Implies(condPath, z3.And(*condRv)))
            
        condProg+=self.choiceRunConditions()
        condProg+=self.globalUnknownsCondition()
        return condProg

    def genInput(self,k):

        funcData=[]
    
        solver=z3.Solver()
        solCond=[]
        while self.context.nextPath():
            #print self.func
            
            res=self.func.__call__(*self.inVars)
            condRv=self.matchOut(res)
            condPath=self.pathCondition()
            print condPath
            #z3.Implies(condPath, condRv)

            varHack=[]
            for iv in self.inVars:
                varHack.append(iv==z3.Int('tmp_'+str(iv)))
                
            condPath=z3.And(condPath,*varHack)
                
            for vin in self.inVars:
                solver.reset()
                solver.add(condPath)
                solver.add(*solCond)
                i=0
                while(solver.check() and i<k*len(self.inVars)):
                    m=solver.model()
                    #print m
                    funcData.append([m[x].as_long() for x in self.inVars])
                    solver.add(vin!=m[vin]);
                    if not solver.check():
                        # Remove last condition... caued to fail.
                        solver.assertions().pop()
                        # And go for next one
                        break
                    solCond.append(z3.And(*[ x!=m[x] for x in self.inVars ]))
                    i+=1

                # Now again, across all vars
                while(solver.check() and i<k*len(self.inVars)):
                    m=solver.model()
                    #print m
                    funcData.append([m[x] for x in self.inVars])
                    cc=z3.And(*[ x!=m[x] for x in self.inVars ])
                    solver.add(cc);
                    if not solver.check():
                        # Remove last condition... caued to fail.
                        solver.assertions().pop()
                        # And go for next one
                        break
                    solCond.append(cc)
                    i+=1
            

        return funcData
    
    def genData(self,inData):
        outData=[]
        f=self.orig_f()
        for dt in inData:
            res=f.__call__(*(dt))
            res=list(res)
            outData.append([dt,res])

        return outData