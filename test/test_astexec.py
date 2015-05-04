'''
Created on 29.04.2015

@author: schultschik
'''
import unittest
import astexec
import ast


# TODO: testcase is failing... why?
class TestExecPath(unittest.TestCase):
    
    def testAdd(self):
        ep=astexec.ExecutionPath()
        ep.addBranch(0, 1, 1)
        ep.addBranch(1, 1, 1)
        ep.addBranch(5, 1, 1)
        
        self.assertEqual(3,len(ep.cond))

        ep2=astexec.ExecutionPath()
        ep2.addBranch(0, 1, 1)
        ep2.addBranch(1, 1, 1)
        ep2.addBranch(5, 1, 1)

        self.assertTrue(ep.samePath(ep2))
        
        ep2.addBranch(3, 0, 1)

        self.assertFalse(ep.samePath(ep2))

class TestFuncExec(unittest.TestCase):
    
    s="""def f(x):
        return x+1
    """

    s2="""def f(x):
        if x>0:
            return x+1
        return x-1
    """

    s3="""def f(x):
        y='-'
        if x>5:
            if(x>10):
                y='11'
                if(x>15):
                    y='111'
            else:
                y='10'
                if(x>20):
                    y='101'
        else:
            y='0'
        y+='+'
        if x>30:
            y+='1'
        else:
            if x>50:
                y+='01'
            else:
                y+='00'
        return y
    """

    
    def testExec(self):
        fe=astexec.FunctionExecutor(ast.parse(self.s), 'f')
        self.assertEqual(3,fe.call(2))
        
    def testGenData(self):
        fe=astexec.FunctionExecutor(ast.parse(self.s), 'f')
        out=fe.genData([[1],[2],[3]])
        self.assertEqual(1, out[0][0][0])
        self.assertEqual(2, out[1][0][0])
        self.assertEqual(3, out[2][0][0])
        self.assertEqual(2, out[0][1][0])
        self.assertEqual(3, out[1][1][0])
        self.assertEqual(4, out[2][1][0])

    def testInstrExec(self):
        fe=astexec.InstrumentedExecutor(ast.parse(self.s2), 'f')
        fe.nextPath()
        self.assertEqual(3,fe.call(4))
        self.assertEqual(-2,fe.call(-1))
        
        fe.nextPath()
        self.assertEqual(3,fe.call(2))
        self.assertEqual(-2,fe.call(-3))

        self.assertFalse(fe.nextPath())
        
        
    def testPathIter(self):
        res=[]
        fe=astexec.InstrumentedExecutor(ast.parse(self.s3), 'f')
        log=astexec.PathLog()
        while (fe.nextPath()):
            (rv,p)=fe.callExt(0)
            if log.addPath(p):
                res.append(rv)

        self.assertEquals(15,len(res))        

        

if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testName']
    unittest.main()