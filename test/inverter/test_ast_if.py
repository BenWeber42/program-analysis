'''
Created on 04.04.2015

@author: schultschik
'''
import unittest
import ast


class Test(unittest.TestCase):

    code="def f(x):\n" \
         "  if x>0:\n" \
         "    y=2*x\n" \
         "  else:\n" \
         "    y=x*x\n" \
         "  return y+1"

    def testAst(self):
        tree=ast.parse(Test.code, "bla")
        print ast.dump(tree)
        
        expr=tree.body[0].body[0].value
        expr=ast.Expression(expr)
        
        expr2=compile(expr, "<bla>", "eval")
        print eval(expr2,{"x":2})


if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testAst']
    unittest.main()