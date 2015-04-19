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
import inspect

s="""
def f(x,y):
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

# Assignment inside if?
class InstrumentingVisitor(ast.NodeTransformer):
    def __init__(self):
        self.refCnt=0
        self.outer=-1

    ctx_var=ast.Name(id='cond_context',ctx=ast.Load())
    
    def gen_instr_call(self,s):
        mark=ast.Str(s=s)
        func=ast.Attribute(value=InstrumentingVisitor.ctx_var,attr='instrument',ctx=ast.Load())
        return ast.Call(func=func,args=[ast.Num(n=self.refCnt),mark],keywords=[])

    def gen_wrap_call(self,t):
        func=ast.Attribute(value=InstrumentingVisitor.ctx_var,attr='wrap_condition',ctx=ast.Load())
        return ast.Call(func=func,args=[ast.Num(n=self.refCnt),t,ast.Num(n=self.outer)],keywords=[])
        
    def generic_visit(self, node):
        print ast.dump(node)
        prevOuter=self.outer
        if node.__class__.__name__ == 'If' :
            print ast.dump(node.test)
            t=node.test
            node.test=self.gen_wrap_call(t)
            node.body.insert(0,ast.Expr(value=self.gen_instr_call("if")))
            node.body.append(ast.Expr(value=self.gen_instr_call("endif")))
            if node.orelse:
                node.orelse.insert(0,ast.Expr(value=self.gen_instr_call("else")))
                node.orelse.append(ast.Expr(value=self.gen_instr_call("endelse")))
                
            self.outer=self.refCnt
            self.refCnt=self.refCnt+1

        print node.__class__.__name__
        for c in ast.iter_child_nodes(node):
            self.visit(c)
            
        self.outer=prevOuter
        return node



class SymExecContext:
    def __init__(self,count):
        self.cond={}
        self.fullcond={}
        self.choice=-1
        self.maxChoice=1<<count


    def wrap_condition(self,ref,cond_in,outer):
        cond=cond_in
        rv=(self.choice>>ref)&1
        if not rv:
            cond=z3.Not(cond_in)
            
        cond_conj=cond
        if outer != -1:
            cond_conj=z3.And(cond,self.cond[outer])
        self.cond[ref]=cond
        self.fullcond[ref]=cond_conj
        #print "condition {0} {1} {2}\n".format(ref,outer,cond_conj)
        return rv;
    
    def instrument(self,ref,label):
        pass
        #print "instrument {0}, label={1}\n".format(ref,label)
    
    def nextPath(self):
        self.choice=self.choice+1
        self.fullcond={}
        self.cond={}
        return self.choice<self.maxChoice
        

def main():
    tree=ast.parse(s)
    print ast.dump(tree.body[0])
    vv=InstrumentingVisitor()
    vv.visit(tree.body[0])
    print ast.dump(tree.body[0])
    ast.fix_missing_locations(tree)
    comp=compile(tree, "<no>", "exec")
    cc=SymExecContext(vv.refCnt)
    sc={"cond_context":cc}
    sc2={}
    exec(comp,sc,sc2)
    spec=inspect.getargspec(sc2['f'])
    a=[]
    for i in range(0,len(spec.args)):
        a.append(z3.Int('In'+str(i)))
    while cc.nextPath():
        res=sc2['f'].__call__(*a)
        print res,cc.cond

if __name__ == '__main__':
    main()
