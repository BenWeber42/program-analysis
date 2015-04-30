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
from compiler.ast import Node

#
#
#   if x==0:
#      ...
#   else:
#      y=1/x
#
#
#   f(z3.Int('_X'))
# ....
#   if(x==0):  #== z3.Expr('_X==0')
#  -->
#   if(cond_context.wrap_condition(label,x==0):
#
# ...
#
#        x=x+1  #== z3.Expr('_X+1')
#             if cond_context.wrap_condition(label2,x>25):  #== z3.Expr('_X+1>25')
#
# expects global var cond_context: class with methods 
#    instrument(self,refNo,marker[[e.g. if endif else endelse]])
#    wrap_condition(self,refNo,condition,refToOuterIf)
#
#  Use  instance.visit(astTree) to start adding instrumentation
#
class InstrumentingVisitor(ast.NodeTransformer):
    """
    AST Node transformer that inserts instrumentation into the tree.
     * All instrumentation is implemented as method call on variable "cond_context". 
     * If conditions are wrapped by "cond_context.wrap_condition(<<ReferenceId>>,<<original condition>>,<<OuterIfId>>)
       * ReferenceId: Each wrapped condition is associated with an id (counting upward from 0).
       * original condition: AST tree of the original condition
       * OuterIfID: In case of nested ifs: The ReferenceID of the next ancestor IF in the tree
     * Additionally transforms unknown_int and unknown_choice into a method call and adds reference IDs:
       --> cond_context.unknown_choice(<<ReferenceId>>,<<original args>>)
       --> cond_context.unknown_int(<<ReferenceId>>
       
    TODOS:
    * Currently same reference ID or even same class for unknowns and if instrumentation --> separate
    """
    
    def __init__(self):
        self.refCnt=0
        self.refCntUnknowns=0
        self.outer=-1
        self._unknowns={}

    ctx_var=ast.Name(id='cond_context',ctx=ast.Load())
    
    @property
    def refLength(self):
        """Contains the last ReferenceId used for IFs +1 (array length semantics)"""
        return self.refCnt
    
    @property
    def unknowns(self):
        """returns a map unknownId --> corresponding Call node in the AST tree"""
        return self._unknowns
    
    def gen_wrap_call(self,t):
        """Generate the condition wrapper call. t is the AST expression tree for the conditional"""
        func=ast.Attribute(value=InstrumentingVisitor.ctx_var,attr='wrap_condition',ctx=ast.Load())
        return ast.Call(func=func,args=[ast.Num(n=self.refCnt),t,ast.Num(n=self.outer)],keywords=[])
        
    def generic_visit(self, node):
        """ 
           Override the visitor's generic method to find If conditions and Calls in the tree
           TODO: better override visit_If and visit_Call instead.
        """
        #print ast.dump(node)
        # keep track of nested IFs
        prevOuter=self.outer
        
        if node.__class__.__name__ == 'Call' and node.func.__class__.__name__ == 'Name':
            if node.func.id=='unknown_int':
                node.func=ast.Attribute(value=InstrumentingVisitor.ctx_var,attr="unknown_int",ctx=ast.Load())
                node.args.insert(0,ast.Num(n=self.refCntUnknowns))
                self._unknowns[self.refCntUnknowns]=node
                self.refCntUnknowns+=1
            elif node.func.id=='unknown_choice': 
                node.func=ast.Attribute(value=InstrumentingVisitor.ctx_var,attr="unknown_choice",ctx=ast.Load())
                node.args.insert(0,ast.Num(n=self.refCntUnknowns))
                self._unknowns[self.refCntUnknowns]=node
                self.refCntUnknowns+=1
        elif node.__class__.__name__ == 'If' :
            #print ast.dump(node.test)
            t=node.test
            node.test=self.gen_wrap_call(t)
            self.outer=self.refCnt
            self.refCnt=self.refCnt+1

        #print node.__class__.__name__
        # Go through all children... original method would do this already.
        for c in ast.iter_child_nodes(node):
            self.visit(c)
            
        # keep track of nested IFs
        self.outer=prevOuter
        return node


class TemplateTransformer(ast.NodeTransformer):
    """
    Replaces unknown_int and unknown_choice with the supplied values
    Requires that the visited AST tree has been instrumented (using InstrumentingVisitor) as the
    replacements are matched by ReferenceId.
    """
    
    def __init__(self,unknown_vars, unknown_choices):
        """
        Constructor. Requires two maps to replace unknown_ints and unknown_choices:
         * unknown_ints: ReferenceId -> integer literal to replace with
         * unknwon_choice: ReferenceId -> argument of the function to substitute the call with
           e.g. cond_context.unknown_choice(4,v0,v1,v2) ( {4:1} ) --> replace by "v1" in AST
        """
        self.unknown_vars=unknown_vars
        self.unknown_choices=unknown_choices

    def visit_Call(self, node):
        """
        called from generic_visitor during visit for all calls. only reacts on unknown_... methods
        """
        rv=node
        if node.func.attr=='unknown_int':
            ref=node.args[0].n
            val=self.unknown_vars[ref]
            rv=ast.Num(n=val)
        elif node.func.attr =='unknown_choice': 
            ref=node.args[0].n
            sel=self.unknown_choices[ref]
            rv=node.args[sel+1]
        elif node.func.attr =='wrap_condition': 
            rv=node.args[1]

        return rv


