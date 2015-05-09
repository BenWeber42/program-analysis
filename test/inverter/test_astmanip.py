'''
Created on 29.04.2015

@author: schultschik
'''
import unittest
import ast
from pysyn import *


def compileFkt(astTree,context,fname):
    ast.fix_missing_locations(astTree)
    comp=compile(astTree, "<no>", "exec")
    sc={"cond_context":context}
    sc2={}
    exec(comp,sc,sc2)
    #spec=inspect.getargspec(sc2[fname])
    return sc2[fname]

    
class Test(unittest.TestCase):

    data_wrap="""
def f(a,b):
    if a:
        pass
    else:
        pass
    """

    data_tpl="""
def f(a,b):
    if a==cond_context.unknown_choice(123,101,102,103,104):
        return 1111
    else:
        return cond_context.unknown_int(321)
    """

    
    class TestContext:
        def __init__(self,tc,expected_id,expected_cond_val, expected_outer,rv={}):
            self.tc=tc
            self.expected_id=expected_id
            self.expected_cond_val=expected_cond_val
            self.expected_outer=expected_outer
            self.wrapCalled=0
            self.rv=rv
        def wrap_condition(self,ref,cond_in,outer):
            self.wrapCalled+=1
            self.tc.assertEqual(self.expected_id,ref)
            self.tc.assertEqual(self.expected_cond_val,cond_in)
            self.tc.assertEqual(self.expected_outer,outer)
            if self.rv.has_key(ref):
                return self.rv[ref]
            else:
                return cond_in
            

    def testInstrument(self):
        visitor=InstrumentingVisitor()
        tree=ast.parse(self.data_wrap)
        visitor.visit(tree)
        ctx=self.TestContext(self,0,1,-1)
        f=compileFkt(tree, ctx, "f")
        f.__call__(1,0)
        self.assertEqual(1,ctx.wrapCalled)

    def testTemplate(self):
        visitor=TemplateTransformer({321:888}, {123:2})
        tree=ast.parse(self.data_tpl)
        visitor.visit(tree)
        f=compileFkt(tree, None, "f")
        self.assertEqual(1111,f.__call__(103,0))
        self.assertEqual(888,f.__call__(102,0))

if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testName']
    unittest.main()