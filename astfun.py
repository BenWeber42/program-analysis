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
import ast

s="""
def f(x,y):
    t=x+y
    if t> 0:
        p=1
    else:
        p=2
    return 0,p
"""

# Assignment inside if?
class v(ast.NodeTransformer):
    def generic_visit(self, node):
        print ast.dump(node)
        if node.__class__.__name__ == 'If' :
            print ast.dump(node.test)
            t=node.test
            node.test=ast.Function()

        print node.__class__.__name__
        for c in ast.iter_child_nodes(node):
            self.visit(c)
        return node

def main():
    tree=ast.parse(s)
    print ast.dump(tree.body[0])
    vv=v()
    vv.visit(tree.body[0])
    print ast.dump(tree.body[0])

if __name__ == '__main__':
    main()
