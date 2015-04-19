#-------------------------------------------------------------------------------
# Name:        astmanip
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

#
# expects global var cond_context: class with methods 
#    instrument(self,refNo,marker[[e.g. if endif else endelse]])
#    wrap_condition(self,refNo,condition,refToOuterIf)
#
#  Use  instance.visit(astTree) to start adding instrumentation
#
class InstrumentingVisitor(ast.NodeTransformer):
    def __init__(self):
        self.refCnt=0
        self.outer=-1

    ctx_var=ast.Name(id='cond_context',ctx=ast.Load())
    
    # Generate the instrumentation call for AST
    def gen_instr_call(self,s):
        mark=ast.Str(s=s)
        func=ast.Attribute(value=InstrumentingVisitor.ctx_var,attr='instrument',ctx=ast.Load())
        return ast.Call(func=func,args=[ast.Num(n=self.refCnt),mark],keywords=[])

    # Generate the condition wrapper call. t is the AST expression tree for the conditional
    def gen_wrap_call(self,t):
        func=ast.Attribute(value=InstrumentingVisitor.ctx_var,attr='wrap_condition',ctx=ast.Load())
        return ast.Call(func=func,args=[ast.Num(n=self.refCnt),t,ast.Num(n=self.outer)],keywords=[])
        
    def generic_visit(self, node):
        #print ast.dump(node)
        prevOuter=self.outer
        if node.__class__.__name__ == 'If' :
            #print ast.dump(node.test)
            t=node.test
            node.test=self.gen_wrap_call(t)
            node.body.insert(0,ast.Expr(value=self.gen_instr_call("if")))
            node.body.append(ast.Expr(value=self.gen_instr_call("endif")))
            # NOTE: elif are expanded to If(..., orelse=) after AST
            if node.orelse:
                node.orelse.insert(0,ast.Expr(value=self.gen_instr_call("else")))
                node.orelse.append(ast.Expr(value=self.gen_instr_call("endelse")))
                
            self.outer=self.refCnt
            self.refCnt=self.refCnt+1

        #print node.__class__.__name__
        for c in ast.iter_child_nodes(node):
            self.visit(c)
            
        self.outer=prevOuter
        return node


#
# Context class used when executing AST trees prepared by InstrumentingVisitor
#
# Provides instrumentation/wrapper functions injected in AST
# 
# Provides mechanism to iterate through all possible if trees by changing the
# result of the conditional in the wrapper (see nextPath())
#
# Use:
#    cc=SymExecContext(vv.refCnt)
#    sc={"cond_context":cc}
#    sc2={}
#    exec(comp,sc,sc2)
#    rv=sc2['f'].__call__(*args)
#
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

    def resetPath(self):
        self.choice=-1
        self.fullcond={}
        self.cond={}
