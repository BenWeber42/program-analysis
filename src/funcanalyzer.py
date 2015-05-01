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
#import ast
#import unparse
#from unparse import  * ## REMOVE
from astmanip import * ## REMOVE
from astexec import * ## REMOVE

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
    
    def __init__(self,vars,baseCond=[]):
        """
         vars: list of z3 variables/expressions
         baseCond: base conditions always present
        """
        self.solver=z3.Solver()
        self.previousSolutionConds=[]
        self.baseCond=baseCond
        self.solver.add(*baseCond)
        self.vars=vars
        self.results=[]
    
    
    def reset(self):
        """Reset conditions, but add base conditions and exclude previous solutions"""
        self.solver.reset()
        self.solver.add(*self.baseCond)
        self.solver.add(*self.previousSolutionConds)

    def add(self,*conds):
        """normal add for z3.Solver"""
        self.solver.add(*conds)
        
    def genAvoidCondition(self,inData,forVars=None):
        """
        Generate condition to avoid results for certain variable dimensions
         * inData: list, e.g. previous solution
         * forVars: indices in variable list, rsp. inData.
        returns condition: inData[i]!=vars[i] (i in forVars) 
        """
        if forVars is None:
            forVars=range(0,len(self.vars))
        if len(inData)!=len(self.vars):
            raise "length of data ({0}) and length of input vars ({1}) do not match".format(len(inData),len(self.vars))
        return z3.And(*[ self.vars[i]!=inData[i] for i in forVars ])

    def findSolutionAvoid(self,inData,forVars=None):
        """Find solution avoiding results in certain variable dimensions, see genAvoidCondition"""
        cond=self.genAvoidCondition(inData, forVars)
        return self.findSolution(cond)

    def findSolution(self,*newConds):
        """
        try to find solution. If successful, add exclusion condition, add to result and return data. 
        Else return None, leave solver in original state
        """
        self.solver.push()
        self.solver.add(*newConds);
        if not self.solver.check()==z3.sat:
            # Remove last condition... caued to fail.
            self.solver.pop()
            return None
            # And go for next one
            #break
            
        m=self.solver.model()
        res=[m[x].as_long() for x in self.vars]
        self.previousSolutionConds.append(self.genAvoidCondition(res))
        self.results.append(res)
        return res

    



class FuncAnalyzer:
    """
    Function analyzer/synthesizer
    """
    
    def __init__(self,astTree,fname='f'):
        self.func=InstrumentedExecutor(astTree, fname)
        self.oFunc=FunctionExecutor(astTree, fname)
        
        self.outVars=[]
            
        self.inVars=[]
        for i in range(0,len(self.func.spec.args)):
            self.inVars.append(z3.Int('In'+str(i)))

    def matchVars(self,v,data):
        """
        Utility function to generate a z3 condition for a list
         * v: list of z3 variables (or other expressions)
         * data: list of data items to match with the correpsonding item in v
        return a z3 condition
        """
        cond=[]
        for i in range(0,len(v)):
            cond.append(v[i]==data[i])
        return z3.And(*cond)
    
    def matchOut(self,data):
        """
        Create a z3 condition to match output variables 
        """
        
        # The number of elements returned may vary. --> increase output variable size on demand
        i=len(self.outVars)
        while i<len(data):
            self.outVars.append(z3.Int('Out'+str(i)))
            i=i+1
        return self.matchVars(self.outVars, data)

    def calcForward(self):
        """
        Generate z3 conditions between input and output for all branch paths of given func.
        Uses z3 variables in inVars and outVars.
        """

        pathLog=PathLog()
        condProg=[]
    
        self.func.resetPath()
        while self.func.nextPath():
            #print self.func
            (res,path)=self.func.callExt(*self.inVars)
            if not pathLog.addPath(path):
                # We encountered this path already... No need to add
                continue
            
            condRv=self.matchOut(res)
            condPath=path.pathCondition
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
        """
        Generate input data for given function based on branching conditions.
        Find k*(len(inVars)+1) solutions within each branch. Avoids duplicate solutions between branches
        Branches that show no (or no more) solutions are skipped.
        """
    
        solver=ResultIteratingSolver(self.inVars)
        
        pathLog=PathLog()
        while self.func.nextPath():
            (res,path)=self.func.callExt(*self.inVars)
            if not pathLog.addPath(path):
                continue

            #condRv=self.matchOut(res)
            condPath=path.pathCondition
            print condPath
            #z3.Implies(condPath, condRv)

            varHack=[]
            for iv in self.inVars:
                varHack.append(iv==z3.Int('tmp_'+str(iv)))
                
            condPath=z3.And(condPath,*varHack)

            solver.add(condPath)
            
            inData=solver.findSolution()
            if inData is None:
                # We didn't find any solution
                continue
            
            for i_in in range(0,len(self.inVars)):
                solver.reset()
                solver.add(condPath)
                
                i=0
                while(i<k*len(self.inVars)):
                    # First only exclude one dimension, run through all dimensions
                    inData=solver.findSolutionAvoid(inData, [i_in])
                    if inData is None:
                        break
                    i+=1

            # Now again, across all vars, find whatever other solutions
            while(i<k*len(self.inVars)):
                inData=solver.findSolution(inData)
                if inData is None:
                    break
                i+=1
            

        return solver.results
    
