'''
Created on 29.04.2015

@author: schultschik
'''
import unittest
import ast
import funcsynth
import z3
import astexec


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
    
    def __init__(self,arg):
        unittest.TestCase.__init__(self,arg)
        self.data2=[]
        
        self.data2.append([[1,1],[1,2]])
        self.data2.append([[5,0],[1,2]])

        self.data=[]
        self.data.append([[1,1],[7]])
        self.data.append([[3,0],[9]])

#        self.data.append([[-5,0],[0,1]])
#        self.data.append([[-6,0],[0,1]])


    def testGenTrainer2(self):
        fs=funcsynth.FuncSynthesizer(ast.parse(self.s2), 'f_inv')
        
        cond=fs.genConditionsFrom(self.data2)
        
        #print cond
        solver=z3.Solver()
        solver.add(cond)
        self.assertEqual(z3.sat,solver.check())
        self.assertEqual(1,solver.model()[z3.Int("Num1")].as_long())

    def testGenTrainer(self):
        fs=funcsynth.FuncSynthesizer(ast.parse(self.s), 'f_inv')
        
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
        fs=funcsynth.FuncSynthesizer(ast.parse(self.s2), 'f_inv')
        uki,ukc=fs.extractSolution(m)
        self.assertEqual(1,uki[0])
        self.assertEqual(2,ukc[0])

    def testTemplate(self):
        fs=funcsynth.FuncSynthesizer(ast.parse(self.s), 'f_inv')
        
        tree=fs.template({1:22}, {0:1})
        ff=astexec.FunctionExecutor(tree, 'f_inv')
        self.assertEqual(24,ff.call(11,2))

if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testName']
    unittest.main()