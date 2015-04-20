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
import ast
import unparse
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
        self.tree=astTree

        vv=InstrumentingVisitor()
        vv.visit(astTree)
        #print ast.dump(tree.body[0])
        ast.fix_missing_locations(astTree)
        unparse.Unparser(astTree)
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
            
        condProg+=self.unknownsCondition()
        return condProg

    def genTrainer(self,data):
        
        condProg=[]
    
        while self.context.nextPath():
            #print self.func
            for t in data:
                self.context.resetExec()
                res=self.func.__call__(*(t[0]))
                condRv=[]
                if type(res)=='tuple':
                    for i in range(0,len(res)):
                        condRv.append(res[i]==t[1][i])
                else:
                    condRv.append(res==t[1])
                condPath=self.pathCondition()
                condProg.append(z3.Implies(condPath, z3.And(*condRv)))
            
        condProg+=self.globalUnknownsCondition()
        return condProg

