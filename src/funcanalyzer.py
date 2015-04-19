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
from unparse import  * ## REMOVE
from astmanip import * ## REMOVE

# Test Cases: 
#    Input unrelate output
#    Assembly/disassemly by switch/case
#    Result dep on single in-var --> rest undefined
#    Div 0
#    Overflow

class FuncAnalyzer:
    def __init__(self,astTree):
        self.tree=astTree

        vv=InstrumentingVisitor()
        vv.visit(astTree)
        #print ast.dump(tree.body[0])
        ast.fix_missing_locations(astTree)
        #Unparser(tree)
        comp=compile(astTree, "<no>", "exec")
        self.context=SymExecContext(vv.refCnt)
        sc={"cond_context":self.context}
        sc2={}
        exec(comp,sc,sc2)
        spec=inspect.getargspec(sc2['f'])
        self.func=sc2['f']

        self.outVars=[]
        for i in range(0,len(spec.args)):
            self.outVars.append(z3.Int('Out'+str(i)))
            
        self.inVars=[]
        for i in range(0,len(spec.args)):
            self.inVars.append(z3.Int('In'+str(i)))

    def pathCondition(self):
        return z3.And(*(self.context.cond.values()))


    def matchVars(self,v,data):
        cond=[]
        for i in range(0,len(v)):
            cond.append(v[i]==data[i])
        return z3.And(*cond)
    
    def matchOut(self,data):
        if(len(data)!=len(self.outVars)):
            raise "Expected {0} output fields, got {1}".format(len(self.outVars),len(data))    
        return self.matchVars(self.outVars, data)

    def calcForward(self):
        
        condProg=[]
    
        while self.context.nextPath():
            res=self.func.__call__(*self.inVars)
            condRv=self.matchVars(self.outVars, res)
            condPath=self.pathCondition()
            condProg.append(z3.Implies(condPath, condRv))
        return condProg

