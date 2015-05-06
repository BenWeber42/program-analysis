#!/usr/bin/env python
"""
Carries out several tests involving sample programs.
"""

from os import path
from glob import glob
from traceback import print_exc
from sys import argv
import ast
from pysyn import *

class Sample(FunctionLoader):
    """
    Holds all information about a sample
    
    For a sample expects the following files:
    * <sample>.py - The sample program
    * <sample>.inp - The input vector if it exists
    * <sample>.out - The output vector if it exists
    * <sample>.syn.py - The reference inverse function if it exists
    """

    def __init__(self, p):
        assert path.isfile(p)
        super(Sample, self).__init__(p)

        name, _ = path.splitext(p)

        self.input = name + ".inp"
        self.output = name + ".out"
        self.reference = name + ".ref.py"
        # they are used for lazy initialization
        self.input_vectors = None
        self.output_vectors = None
        self.reference_ast = None
        self.reference_source = None
   
    def has_input(self):
        return path.isfile(self.input)
        
    def has_output(self):
        return path.isfile(self.output)
    
    def has_reference(self):
        return path.isfile(self.reference)
    
    def get_input(self):
        assert self.has_input()
        if self.input == None:
            self.input = load_vectors(self.input)
        return self.input

    def get_output(self):
        assert self.has_output()
        if self.output == None:
            self.output = load_vectors(self.output)
        return self.output
   
    def get_reference_source(self):
        assert self.has_reference()
        if self.reference_source == None:
            self.reference_source = read_file_to_string(self.reference)
        return self.reference_source

    def get_reference(self):
        if self.reference_ast == None:
            self.reference_ast = ast.parse(self.get_reference_source())
        for node in self.reference_ast.body:
            if FunctionLoader.is_template(node):
                return node

class SampleTester:
    
    def __init__(self, sample):
        self.sample = sample
    
    def run(self):
        if self.sample.has_output():
            self.run_solve()
        if self.sample.has_template():
            self.run_syn()


    def run_solve(self):
        ys = self.sample.get_output()
        try:
            xs = solve_app(self.sample.get_source(), ys)
        except:
            print("Command solve failed on sample '%s'!" % self.sample.path)
            print_exc()
        else:
            # verify:
            f = compile_ast(self.sample.get_f())
            
            for x, y in zip(xs, ys):
                if y != "Unsat":
                    y_ref = list(f(*x))
                    if y_ref != y:
                        print "Incorrectly solved f(%s) = (%s) because f(%s) = (%s)!" % (
                            ", ".join(x),
                            ", ".join(y),
                            ", ".join(x),
                            ", ".join(y_ref)
                            )
                # TODO: what about "Unsat"?
                
    def run_syn(self):
        try:
            out = syn_app(self.sample.get_source())
        except:
            print("Command syn failed on sample '%s'!" % self.sample.path)
            print_exc()
        else:
            if not self.sample.has_reference():
                print("Syn yielded on sample '%s':" % self.sample.path)
                print out
                return
            
            actual = find_function(ast.parse(out), "f_inv")
            ref = self.sample.get_reference()

            # could be improved, but seems to suffice
            if ast_to_source(actual) != ast_to_source(ref):
                print("Synthesized solution differs from reference solution!")
                print("Reference Solution:")
                print(ast_to_source(ref))
                print("")
                print("Synthesized Solution:")
                print(ast_to_source(actual))
                print("")


        
if __name__ == "__main__":
    # ugly hack to collect .py files in sub directories
    if len(argv) <= 1:
        tests = glob("./samples/*.py")
        tests += glob("./samples/*/*.py")
        tests += glob("./samples/*/*/*.py")
        tests += glob("./samples/*/*/*/*.py")
    else:
        tests = argv[1:]

    for f in tests:
        # ignore reference solutions
        if f.endswith("ref.py"):
            continue
        test = SampleTester(Sample(f))
        print(">>> Running testcase '%s'" % f)
        test.run()
        print("")
