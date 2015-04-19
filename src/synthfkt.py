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
from funcanalyzer import *

s="""
def f_inv(x,y):
    t=x+unknown_choice(x,y,0,1)
    if t> 0:
        p=1
        if x>2:
            x=x+unknown_int()
        elif x==1:
            y=y+1
        else:
            pass
    else:
        p=2
    return x,p
"""

# Test Cases: 
#    Input unrelate output
#    Assembly/disassemly by switch/case
#    Result dep on single in-var --> rest undefined
#    Div 0
#    Overflow

def main():
    tree=ast.parse(s)
    fa=FuncAnalyzer(tree,'f_inv')
    conds=fa.calcForward()
    solver=z3.Solver()
    #print matchVars(outVars, [1,1])
    print conds
    solver.add(*conds)
    solver.add(fa.matchOut([1,1]))
    if(solver.check()):
        print solver.model()

if __name__ == '__main__':
    main()
