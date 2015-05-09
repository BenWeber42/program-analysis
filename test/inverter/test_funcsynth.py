'''
Created on 29.04.2015

@author: schultschik
'''
import unittest
import ast
import z3
from pysyn import *

class Test(unittest.TestCase):

    s2="""
def f_inv(x,y):
    if x> unknown_int():
        return unknown_int(),unknown_int()
    else:
        return unknown_int(),unknown_int()
    """
    
    s="""
def f(x):
    return x,22
    
def f_inv(x,y):
    return unknown_choice(x,y,0,1)+unknown_int()
    """

    s3="""
def f(x):
    return x,22
    
def f_inv(x,y):
    return unknown_choice(x,y,0,1)+unknown_choice(x,y,0,1)
    """

    
    def __init__(self,arg):
        unittest.TestCase.__init__(self,arg)
        self.data2=[]
        
        self.data2.append([[1,1],[1,2]])
        self.data2.append([[5,0],[1,2]])

        self.data=[]
        self.data.append([[1,1],[7]])
        self.data.append([[3,0],[9]])

        self.data3=[]
        self.data3.append([[1,1],[2]])
        self.data3.append([[3,0],[3]])

#        self.data.append([[-5,0],[0,1]])
#        self.data.append([[-6,0],[0,1]])


    def testGenTrainer2(self):
        fs=FuncSynthesizer(ast.parse(self.s2), 'f_inv')
        
        cond=fs.genConditionsFrom(self.data2)
        
        #print cond
        solver=z3.Solver()
        solver.add(cond)
        self.assertEqual(z3.sat,solver.check())
        self.assertEqual(1,solver.model()[z3.Int("Num1")].as_long())

    def testGenTrainer(self):
        fs=FuncSynthesizer(ast.parse(self.s), 'f_inv')
        
        cond=fs.genConditionsFrom(self.data)
        
        #print cond
        solver=z3.Solver()
        solver.add(cond)
        self.assertEqual(z3.sat,solver.check())
        self.assertEqual(6,solver.model()[z3.Int("Num1")].as_long())
        self.assertEqual(1,solver.model()[z3.Int("Sel0_0")].as_long())

    def testExtractSol(self):
        solver=z3.Solver()
        solver.add(z3.Int('Num0')==1)
        solver.add(z3.Int('Sel0_2')==1)
        solver.add(z3.Int('Sel0_1')==0)
        solver.add(z3.Int('Sel0_0')==0)
        solver.check()
        m=solver.model()
        fs=FuncSynthesizer(ast.parse(self.s2), 'f_inv')
        uki,ukc=fs.extractSolution(m)
        self.assertEqual(1,uki[0])
        self.assertEqual(2,ukc[0])

    def testTemplate(self):
        fs=FuncSynthesizer(ast.parse(self.s), 'f_inv')
        
        tree=fs.template({1:22}, {0:1})
        ff=FunctionExecutor(tree, 'f_inv')
        self.assertEqual(24,ff.call(11,2))
        
    def testStates(self):
        fs=FuncSynthesizer(ast.parse(self.s2), 'f_inv')        
        maxSt=fs.func.choiceMaxStates
        cs=ChoiceState(maxSt)
        self.assertEqual(1,len(list(cs)))

        fs=FuncSynthesizer(ast.parse(self.s), 'f_inv')        
        maxSt=fs.func.choiceMaxStates
        cs=ChoiceState(maxSt)
        states=list(cs)
        self.assertEqual(4,len(states))

        fs=FuncSynthesizer(ast.parse(self.s3), 'f_inv')        
        maxSt=fs.func.choiceMaxStates
        cs=ChoiceState(maxSt)
        states=list(cs)
        self.assertEqual(16,len(states))
        self.assertIn({0:0,1:0},states)
        self.assertIn({0:3,1:2},states)
        self.assertIn({0:3,1:3},states)

    def testGenHypo(self):
        fs=FuncSynthesizer(ast.parse(self.s3), 'f_inv')        
        hypos=fs.genHypotheses()
        self.assertEqual(16,len(hypos))
        hypos[0].nextPath()
        self.assertEqual(2,hypos[0].call(1,99))
        
        hf=fs.genHypoFkt({0:0,1:1})
        hf.nextPath()
        self.assertEqual(100,hf.call(1,99))
        
        (hypos,sols)=fs.solveHypos(self.data3, hypos)
        count=0
        for i,sol in enumerate(sols):
            if sol is None:
                continue
            count+=1
            self.assertEquals(10,FunctionExecutor( fs.template(sol, None,hypos[i]),'f_inv').call(1,9))
        self.assertEqual(2, count)
        
    
#    def testSolveGenerated(self):    
#        fs.solveUnknowns(fd, func)
        

if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testName']
    unittest.main()