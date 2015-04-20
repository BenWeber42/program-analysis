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

s2="""
def f_inv(x,y):
    if x> unknown_int():
        return unknown_int(),unknown_int()
    else:
        return unknown_int(),unknown_int()
    return x,p
"""

s="""
def f_inv(x,y):
    return unknown_choice(x,y,0,1)
"""

# Test Cases: 
#    Input unrelate output
#    Assembly/disassemly by switch/case
#    Result dep on single in-var --> rest undefined
#    Div 0
#    Overflow
#    Nullstellen von polynomen
#    hochgrad-polnome -- nicht umformbar?

def main():
    tree=ast.parse(s)
    fa=FuncAnalyzer(tree,'f_inv')
    conds=fa.genTrainer([((0,1),(0)),((0,-5),(0)),((3,-5),(3))])
    solver=z3.Solver()
    #print matchVars(outVars, [1,1])
    #print conds
    solver.add(*conds)
    print solver.assertions()
    if(solver.check()):
        print solver.model()

if __name__ == '__main__':
    main()
