'''
Created on 29.04.2015

@author: schultschik
'''
import unittest
import ast
import funcanalyzer
import z3


class Test(unittest.TestCase):

    s="""def f(x,y):
        t=x+y
        if t> 0:
            p=1
            if x>2:
                x=x+1
            elif x==1:
                y=y+1
            else:
                pass
        else:
            p=2
        return x,p
    """
    
    def testForward(self):
        tree=ast.parse(self.s)
        fa=funcanalyzer.FuncAnalyzer(tree)
        conds=fa.calcForward()
        solver=z3.Solver()

        print conds
        solver.add(*conds)
        solver.add(fa.matchOut([1,1]))
        self.assertTrue(solver.check())
        self.assertEqual(1,solver.model().eval(fa.inVars[0]))
        self.assertEqual(1,solver.model().eval(fa.inVars[1]))

    def testBacktrackSolver(self):
        x=z3.Int('x')
        solver=funcanalyzer.ResultIteratingSolver([x])
        solver.add(x>0)
        solver.findSolution(x>1)
        self.assertEquals(1,len(solver.results))
        self.assertIs(None,solver.findSolution(x<0))
        solver.findSolution(x>2)
        self.assertEquals(2,len(solver.results))

    def testInputGenerator(self):
        tree=ast.parse(self.s)
        fa=funcanalyzer.FuncAnalyzer(tree)
        
        inData=fa.genInput(2)
        self.assertLessEqual(5, len(inData))
        
    

if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testName']
    unittest.main()