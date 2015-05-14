#!/usr/bin/env python

import z3
import ast
from sys import argv
from pysyn import FunctionLoader


class PathRaises(Exception):
    """
    Denotes that a path will raise an exception and is therefore no longer worth
    exploring.
    """
    pass


class GiveUp(Exception):
    """
    Denotes that the FunctionAnalyzer should give up analyzing a function.
    This may be raised if an irreversible path was found while analyzing
    for the 'syn' command, then it's no longer worth exploring other paths.
    """
    pass


class FunctionAnalyzer:
    
    """
    Creates Path objects for a function
    """
    
    def __init__(self, f):
        self.f = f
        
        # fetch parameters
        self.input = map(lambda p: z3.Int(p.id), f.args.args)

        self.solver = z3.Solver()
        # initialize argument constraint: x in [1000, -1000]
        self.solver.add(z3.And(*[p >= 1000 for p in self.input]))
        self.solver.add(z3.And(*[p <= 1000 for p in self.input]))

        # add parameters to store
        self.store = dict(zip(map(str, self.input), self.input)) 
        
        self.paths = []
        self.reachable = z3.sat
        self.return_size = -1

        self.is_irreversible = False
        self.migh_be_irreversible = False
        self.irreversible_path_constraints = []
    

    def analyze(self, give_up_on_irreversible_path = False):
        self.give_up_on_irreversible_path = give_up_on_irreversible_path

        try:
            self.block(self.f.body)
        except GiveUp:
            pass
        except PathRaises:
            assert((self.solver.assertions()) == 0)
            self.is_irreversible = True


    def check_return_size(self, size):
        if self.return_size != -1 and self.return_size != size:
            raise Exception("Function is not part of the valid python subset due to unequal size of return tuples!")
        else:
            self.return_size = size
    

    def update_reachable(self):
        self.reachable = self.solver.check()


    def block(self, block):
        if len(block) > 0:
            self.statement(block[0], block[1:])
        else:
            # path that doesn't end with a return statement!
            raise Exception("Function is not part of the valid python subset due to a missing return!")
    

    def statement(self, stmt, block):

        if type(stmt).__name__ == 'Return':
            self._return(stmt, block)

        elif type(stmt).__name__ == 'If':
            self._if(stmt, block)

        elif type(stmt).__name__ == 'Assign':
            self._assign(stmt, block)

        else:
            raise Exception('Invalid statement: ' + ast.dump(stmt))
    

    def _return(self, _return, block):
        
        expr = self.expression(_return.value)
        
        if isinstance(expr, tuple):
            self.check_return_size(len(tuple))
        else:
            self.check_return_size(1)

        # TODO: create path
    

    def _if(self, _if, block):
        
        # TODO: handle PathRaises

        # create check point
        self.solver.push()
        store = self.store.copy()
        reachable = self.reachable

        # fetch condition
        test = self.expression(_if.test)

        # handle true branch
        self.solver.add(test)
        self.update_reachable()
        
        if self.reachable == z3.sat or self.reachable == z3.unknown:
            # explore true branch
            self.explore_path(_if.body + block)
            
        # reset back to checkpoint
        self.solver.pop()
        self.store = store
        self.reachable = reachable
        
        # handle false branch
        if not _if.orelse:
            self.explore_path(block)
            return

        self.solver.add(z3.Not(test))
        self.update_reachable()
        
        if self.reachable == z3.sat or self.reachable == z3.unknown:
            # explore false branch
            self.explore_path(_if.orelse + block)
    
        self.solver.pop()
    
    def explore_path(self, block):
        try:
            self.block(block)
        except PathRaises:
            # TODO: handle problems
            if self.reachable == z3.sat:
                pass


    def _assign(self, assign, block):
        assert(len(assign.targets) == 1)  # Disallow a = b = c syntax
            
        target = self.assignable_expression(assign.targets[0])
        value = self.expression(assign.value)

        target_is_tuple = isinstance(target, tuple)
        value_is_tuple = isinstance(value, tuple)

        if target_is_tuple and value_is_tuple:
            if len(value) != len(target):
                # unequal size of tuples!
                raise PathRaises()

            for t, v in zip(value, target):
                self.store[t] = v
            
        elif not target_is_tuple and not target_is_tuple:
            self.store[target] = value

        else:
            # assignment of target and value have different types!
            raise PathRaises()
        
        self.block(block)
    
    
    def assignable_expression(self, expr):
        
        if type(expr).__name__ == 'Name':
            return expr.id

        if type(expr).__name__ == 'Tuple':
            return tuple(map(self.assignable_expression, expr.elts))
        
        raise Exception("Tried to assign to non-assignable expression! " + ast.dump(expr))
    
    
    def expression(self, expr):

        if type(expr).__name__ == 'Tuple':
            return tuple(map(self.expression, expr.elts))

        if type(expr).__name__ == 'Name':
            if self.store.has_key(expr.id):
                return self.store[expr.id]
            
            # variable doesn't exist, will raise a ValueError!
            raise PathRaises()

        if type(expr).__name__ == 'Num':
            return expr.n

        if type(expr).__name__ == 'BinOp':
            left = self.expression(expr.left)
            right = self.expression(expr.right)
            
            if type(expr.op).__name__ == 'Add':
                return left + right
            if type(expr.op).__name__ == 'Sub':
                return left - right
            if type(expr.op).__name__ == 'Mult':
                return left*right
            if type(expr.op).__name__ == 'Div':

                # check for division by zero
                division_by_zero = self.solver.check(right == 0)
                
                # TODO: implement
                if division_by_zero == z3.sat:
                    pass
                elif division_by_zero == z3.unknown:
                    pass
                else:
                    pass

                return left/right

        if type(expr).__name__ == 'UnaryOp':
            if type(expr.op).__name__ == 'Not':
                out = "not "
            if type(expr.op).__name__ == 'USub':
                out = "-"
            out += "(" + self.expression(expr.operand) + ")"
            return out

        if type(expr).__name__ == 'Compare':
            assert(len(expr.ops) == 1)  # Do not allow for x == y == 0 syntax
            assert(len(expr.comparators) == 1)

            out = "(" + self.expression(expr.left) + ")"

            op = expr.ops[0]
            if type(op).__name__ == 'Eq':
                out += " == "
            if type(op).__name__ == 'NotEq':
                out += " != "
            if type(op).__name__ == 'Gt':
                out += " > "
            if type(op).__name__ == 'GtE':
                out += " >= "
            if type(op).__name__ == 'Lt':
                out += " < "
            if type(op).__name__ == 'LtE':
                out += " <= "

            out += "(" + self.expression(expr.comparators[0]) + ")"
            return out

        if type(expr).__name__ == 'BoolOp':
            operands = map(lambda expr: "(" + self.expression(expr) + ")", expr.values)
            if type(expr.op).__name__ == 'And':
                return " and ".join(operands)
            if type(expr.op).__name__ == 'Or':
                return " or ".join(operands)

        raise Exception('Invalid expression: ' + ast.dump(expr))


class Path:
    
    """
    Entity class that represents a path
    """
    
    def __init__(self, input, output, constraints, relation):
        assert isinstance(input, list)
        assert isinstance(output, list)
        assert isinstance(constraints, list)
        assert isinstance(relation, list)

        self.input = input
        self.output = output
        self.constraints = constraints
        self.relation = relation


if __name__ == "__main__":
    if len(argv) <= 1 or "--help" in argv:
        print("Usage: %s [--help] [file]" % argv[0])
        print("")
        print("   --help   prints this help message and exits.")
        print("   [file]   Creates a dataset of output values that achieves 100% path coverage")
        print("            for a python function 'f' in [file].")
    
    else:
        f = FunctionLoader(argv[1]).get_f()