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


import re
import z3
import inspect
import unparse
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
def f(x):
    return x,22
    
def f_inv(x,y):
    return unknown_choice(x,y,0,1)+unknown_int()
"""

# Test Cases: 
#    Input unrelate output
#    Assembly/disassemly by switch/case
#    Result dep on single in-var --> rest undefined
#    Div 0
#    Overflow
#    Nullstellen von polynomen
#    hochgrad-polnome -- nicht umformbar?

def extractSolution(m):
    unknown_vars={}
    unknown_choices={}
    pat_num=re.compile('^Num(\d+)$')
    pat_sel=re.compile('^Sel(\d+)_(\d+)$')
    for v in m.decls():
        nmatch=pat_num.match(str(v))
        if nmatch:
            unknown_vars[int(nmatch.group(1))]=m[v].as_long()
            continue
        
        smatch=pat_sel.match(str(v))
        if smatch:
            if m[v].as_long()==0:
                continue
            ref=int(smatch.group(1))
            sel=int(smatch.group(2))
            
            unknown_choices[ref]=sel
            
    return unknown_vars,unknown_choices

def main():
    tree=ast.parse(s)
    
    fa2=FuncAnalyzer(tree,'f')
    fd=fa2.genInput(3)
    fd=fa2.genData(fd)
    
    fa=FuncAnalyzer(tree,'f_inv')
    #conds=fa.genTrainer([((0,1),(0)),((0,-5),(0)),((3,-5),(3))])
    conds=fa.genTrainer(fd)
    solver=z3.Solver()
    #print matchVars(outVars, [1,1])
    #print conds
    g=z3.Goal()
    g.add(*conds)
    c2=g.simplify()
    solver.add(c2)
    #print solver.assertions()
    if not solver.check():
        print "Unsat"
        exit
    
    m=solver.model()
    
    unknown_vars,unknown_choices=extractSolution(m)

    tr=fa.template(unknown_vars, unknown_choices)
    unparse.Unparser(tr)

if __name__ == '__main__':
    main()
