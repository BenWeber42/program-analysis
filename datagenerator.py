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
        self.input_names = set(map(lambda p: p.id, f.args.args))

        self.solver = z3.Solver()
        # initialize argument constraint: x in [1000, -1000]
        self.solver.add(z3.And(*[p >= -1000 for p in self.input]))
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
            # must contain only the starting assumptions x in [-1000, 1000]
            assert(len(list(self.solver.assertions())) == 2)
            self.is_irreversible = True


    def check_return_size(self, size):
        if self.return_size != -1 and self.return_size != size:
            raise Exception("Function is not part of the valid python subset due to unequal size of return tuples!")
        else:
            self.return_size = size
    

    def update_reachable(self):
        self.reachable = self.solver.check()
        
    
    def quick_check(self, *constraints):
        self.solver.push()
        self.solver.add(constraints)
        result = self.solver.check()
        self.solver.pop()
        return result


    def block(self, block):
        if len(block) > 0:
            self.statement(block[0], block[1:])
        else:
            if self.reachable == z3.sat:
                # path that doesn't end with a return statement!
                raise Exception("Function is not part of the valid python subset due to a missing return!")
            elif self.reachable == z3.unknown:
                # if we don't know whether a path is reachable
                # but it doesn't end with a return statement, we will assume
                # that it's not reachable, because it's clearly specified
                # that we're working with a python subset where every path
                # contains at least one return statement.
                pass
            else:
                assert(False)
    

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
            self.check_return_size(len(expr))
            output = list(expr)
        else:
            self.check_return_size(1)
            output = [expr]
            
        relation = []
        outvariables = []

        for i in xrange(len(output)):
            
            outname = "y" + str(i + 1)
            
            # avoid collisions with existing variables
            while outname in self.input_names:
                outname = "__" + outname
    
            outvariable = z3.Int(outname)
            outvariables.append(outvariable)
            relation.append(outvariable == output[i])
        
        path = Path(self.input, outvariables, self.solver.assertions(), relation)
        self.paths.append(path)

    def _if(self, _if, block):
        
        # create check point
        self.solver.push()
        store = self.store.copy()
        reachable = self.reachable

        # fetch condition
        test = self.expression(_if.test)

        # handle true branch
        self.solver.add(test)
        self.update_reachable()
        
        # explore true branch
        if self.reachable == z3.sat or self.reachable == z3.unknown:
            self.explore_path(_if.body + block)
            
        # reset back to checkpoint
        self.solver.pop()
        self.store = store
        self.reachable = reachable

        # handle false branch
        self.solver.push()
        self.solver.add(z3.Not(test))
        self.update_reachable()
        
        # explore false branch
        if self.reachable == z3.sat or self.reachable == z3.unknown:

            if not _if.orelse:
                self.explore_path(block)
            else:
                self.explore_path(_if.orelse + block)
    
        self.solver.pop()
    

    def explore_path(self, block):
        try:
            self.block(block)
        except PathRaises:
            self.irreversible_path_constraints.append(list(self.solver.assertions()))
            if self.reachable == z3.sat:
                self.is_irreversible = True
                if self.give_up_on_irreversible_path:
                    raise GiveUp()
            elif self.reachable == z3.unknown:
                self.migh_be_irreversible = True
            else:
                assert(False)


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

            for v, t in zip(value, target):
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
                
                # for some reasons it seems that add with check seems to produce
                # better results than check with assumptions

                # can x be non-zero?
                non_zero = self.quick_check(right != 0)
                if non_zero == z3.sat or non_zero == z3.unknown:
                    
                    # check for division by zero
                    division_by_zero = self.quick_check(right == 0)
                    
                    # handle potential division by zero
                    if division_by_zero == z3.sat:
                        constraint = list(self.solver.assertions())
                        constraint.append(right == 0)
                        self.irreversible_path_constraints.append(constraint)
    
                        self.is_irreversible = True
                        if self.give_up_on_irreversible_path:
                            raise GiveUp()
    
                    elif division_by_zero == z3.unknown:
                        constraint = list(self.solver.assertions())
                        constraint.append(right == 0)
                        self.irreversible_path_constraints.append(constraint)
    
                        self.migh_be_irreversible = True
    
                    else:
                        # x can't be 0, so everything's good
                        pass

                    # continue with assumption that x != 0
                    self.solver.add(right != 0)
                    self.reachable = non_zero
                    
                    return left/right

                else:
                    # x can't be non-zero
                    raise PathRaises

        if type(expr).__name__ == 'UnaryOp':
            operand = self.expression(expr.operand)
            if type(expr.op).__name__ == 'Not':
                return z3.Not(operand)
            if type(expr.op).__name__ == 'USub':
                return -operand
            if type(expr.op).__name__ == 'UAdd':
                return operand

        if type(expr).__name__ == 'Compare':
            assert(len(expr.ops) == 1)  # Do not allow for x == y == 0 syntax
            assert(len(expr.comparators) == 1)
            
            left = self.expression(expr.left)
            right = self.expression(expr.comparators[0])

            op = expr.ops[0]
            if type(op).__name__ == 'Eq':
                return left == right
            if type(op).__name__ == 'NotEq':
                return left != right
            if type(op).__name__ == 'Gt':
                return left > right
            if type(op).__name__ == 'GtE':
                return left >= right
            if type(op).__name__ == 'Lt':
                return left < right
            if type(op).__name__ == 'LtE':
                return left <= right

        if type(expr).__name__ == 'BoolOp':
            operands = expr.values

            if type(expr.op).__name__ == 'And':
                real_operands = []
                for operand in operands:
                    operand = self.expression(operand)
                    if self.quick_check(operand) == z3.unsat:
                        # we could prove that the operand is false
                        # so therefore due to python's short-circuit and operator
                        # the remaining operators don't need to be evaluated
                        # anymore
                        break
                    else:
                        real_operands.append(operand)

                return z3.And(*real_operands)

            if type(expr.op).__name__ == 'Or':
                
                real_operands = []
                for operand in operands:
                    operand = self.expression(operand)
                    if self.quick_check(z3.Not(operand)) == z3.unsat:
                        # we could prove that the operand cannot be false
                        # thus the operand is always true
                        # so therefore with python's short-circuit or operator
                        # the remaining operands don't need to be evaluated
                        # anymore
                        break
                    else:
                        real_operands.append(operand)

                return z3.Or(*real_operands)

        raise Exception('Invalid expression: ' + ast.dump(expr))


class Path:
    
    """
    Entity class that represents a path
    """
    
    def __init__(self, input, output, constraints, relation):
        assert isinstance(input, list)
        assert isinstance(output, list)
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
        print("Analyzing file '%s'" % argv[1])

        f = FunctionLoader(argv[1]).get_f()
        
        analyzer = FunctionAnalyzer(f)
        analyzer.analyze()
        
        print("Found %s path(s)" % len(analyzer.paths))
        if analyzer.is_irreversible:
            print(" - is irreversible")
        elif analyzer.migh_be_irreversible:
            print(" - might be irreversible")