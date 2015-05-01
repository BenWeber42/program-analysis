#!/usr/bin/python

from astmanip import *  # # REMOVE
from unparse import *  # # REMOVE
from funcanalyzer import *  # # REMOVE

import re
import ast
import sys
from funcanalyzer import FuncAnalyzer
from funcsynth import FuncSynthesizer

# import z3

WITH_HYPO = True


def solve_app(program, tests):
    p = ast.parse(program)

    # print(ast.dump(p))

    f = find_function(p, 'f')

    fa = FuncAnalyzer(p)

    solver = z3.Solver()
    conds = fa.calcForward()
    for test in tests.split('\n'):
        if len(test) == 0:
            continue
        outdata = [int(x) for x in test.split(' ')]
        solver.reset()

        # print matchVars(outVars, [1,1])

        solver.add(*conds)
        solver.add(fa.matchOut(outdata))

        # print solver.assertions()

        if solver.check() == z3.sat:
            m = solver.model()

            # print m
            # varNames=[str(x) for x in fa.inVars]

            vals = [m[x] for x in fa.inVars]
            print ' '.join([str(x) for x in vals])
        else:
            print 'Unsat\n'


def syn_app(program):
    tree = ast.parse(program)

    funcAnalyzer = FuncAnalyzer(tree, 'f')
    origfunc = FunctionExecutor(tree, 'f')
    funcSynth = FuncSynthesizer(tree, 'f_inv')

    trainingData = funcAnalyzer.genInput(2)
    trainingData = origfunc.genData(trainingData)
    trainingData = funcSynth.reverseData(trainingData)

    print trainingData

    if WITH_HYPO:
        hypos = funcSynth.genHypotheses()
        solutions = funcSynth.solveHypos(trainingData, hypos)
        funcs = funcSynth.templateHypos(hypos, solutions)
        Unparser(find_function(funcs[0].tree, 'f_inv'))
    else:

        unknown_vars, unknown_choices = funcSynth.solveUnknowns(trainingData)
        if unknown_vars is None:
            print 'Unsat'
            return 1

        tr = funcSynth.template(unknown_vars, unknown_choices)
        Unparser(find_function(tr, 'f_inv'))


def find_function(p, function_name):
    assert type(p).__name__ == 'Module'
    for x in p.body:
        if type(x).__name__ == 'FunctionDef' and x.name == function_name:
            return x
    raise Exception('Function %s not found' % function_name)


def eval_f(f, indata):
    assert type(f).__name__ == 'FunctionDef'
    current = {}

    # print(ast.dump(f))

    eval_f.returned = False
    eval_f.return_val = []

    def run_expr(expr):
        if type(expr).__name__ == 'Tuple':
            r = []
            for el in expr.elts:
                r.append(run_expr(el))
            return tuple(r)
        if type(expr).__name__ == 'Name':
            return current[expr.id]
        if type(expr).__name__ == 'Num':
            return expr.n
        if type(expr).__name__ == 'BinOp':
            if type(expr.op).__name__ == 'Add':
                return run_expr(expr.left) + run_expr(expr.right)
            if type(expr.op).__name__ == 'Sub':
                return run_expr(expr.left) - run_expr(expr.right)
            if type(expr.op).__name__ == 'Mult':
                return run_expr(expr.left) * run_expr(expr.right)
            if type(expr.op).__name__ == 'Div':
                return run_expr(expr.left) / run_expr(expr.right)
        if type(expr).__name__ == 'UnaryOp':
            if type(expr.op).__name__ == 'Not':
                return not run_expr(expr.operand)
            if type(expr.op).__name__ == 'USub':
                return -run_expr(expr.operand)
        if type(expr).__name__ == 'Compare':
            assert len(expr.ops) == 1  # Do not allow for x==y==0 syntax
            assert len(expr.comparators) == 1
            e1 = run_expr(expr.left)
            op = expr.ops[0]
            e2 = run_expr(expr.comparators[0])
            if type(op).__name__ == 'Eq':
                return e1 == e2
            if type(op).__name__ == 'NotEq':
                return e1 != e2
            if type(op).__name__ == 'Gt':
                return e1 > e2
            if type(op).__name__ == 'GtE':
                return e1 >= e2
            if type(op).__name__ == 'Lt':
                return e1 < e2
            if type(op).__name__ == 'LtE':
                return e1 <= e2
        if type(expr).__name__ == 'BoolOp':
            if type(expr.op).__name__ == 'And':
                r = True
                for v in expr.values:
                    r = r and run_expr(v)
                    if not r:
                        break
                return r
            if type(expr.op).__name__ == 'Or':
                r = False
                for v in expr.values:
                    r = r or run_expr(v)
                    if r:
                        break
                return r
        raise Exception('Unhandled expression: ' + ast.dump(expr))

    def run_stmt(stmt):
        if type(stmt).__name__ == 'Return':
            eval_f.returned = True
            eval_f.return_val = run_expr(stmt.value)
            return
        if type(stmt).__name__ == 'If':
            cond = run_expr(stmt.test)
            if cond:
                run_body(stmt.body)
            else:
                run_body(stmt.orelse)
            return
        if type(stmt).__name__ == 'Assign':
            assert len(stmt.targets) == 1  # Disallow a=b=c syntax
            lhs = stmt.targets[0]
            rhs = run_expr(stmt.value)
            if type(lhs).__name__ == 'Tuple':
                assert type(rhs).__name__ == 'tuple'
                assert len(rhs) == len(lhs.elts)
                for el_index in range(len(lhs.elts)):
                    el = lhs.elts[el_index]
                    assert type(el).__name__ == 'Name'
                    current[el.id] = rhs[el_index]
                return
            if type(lhs).__name__ == 'Name':
                current[lhs.id] = rhs
                return
        raise Exception('Unhandled statement: ' + ast.dump(stmt))

    def run_body(body):
        for stmt in body:
            run_stmt(stmt)
            if eval_f.returned:
                return

    # Set initial current:

    assert len(indata) == len(f.args.args)
    arg_index = 0
    for arg in f.args.args:
        assert type(arg).__name__ == 'Name'
        current[arg.id] = indata[arg_index]
        arg_index = arg_index + 1

    # print(current)

    run_body(f.body)
    assert eval_f.returned
    if type(eval_f.return_val).__name__ == 'tuple':
        return eval_f.return_val
    return tuple([eval_f.return_val])


def eval_app(program, tests):
    p = ast.parse(program)

    # print(ast.dump(p))

    f = find_function(p, 'f')
    for test in tests.split('\n'):
        if len(test) == 0:
            continue
        indata = [int(x) for x in test.split(' ')]
        print ' '.join([str(x) for x in eval_f(f, indata)])


def read_file_to_string(filename):
    f = open(filename, 'rt')
    s = f.read()
    f.close()
    return s


def print_usage():
    usage =  """
Usage:
	%(cmd)s eval <python_file> <data_file>
	%(cmd)s solve <python_file> <data_file>
	%(cmd)s syn <python_file>
			""" % {'cmd' : sys.argv[0]}
    print usage


if __name__ == '__main__':
    if len(sys.argv) == 1:
        print_usage()
        exit(1)
    if sys.argv[1] == 'eval':
        eval_app(read_file_to_string(sys.argv[2]), read_file_to_string(sys.argv[3]))
    elif sys.argv[1] == 'solve':
        solve_app(read_file_to_string(sys.argv[2]), read_file_to_string(sys.argv[3]))
    elif sys.argv[1] == 'syn':
        syn_app(read_file_to_string(sys.argv[2]))
    else:
        print 'Unknown command %s' % sys.argv[1]
        print_usage()
        exit(1)

