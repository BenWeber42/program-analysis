#!/usr/bin/env python
"""
Carries out several tests involving sample programs.
"""

from os import path
from glob import glob
from traceback import print_exc
from sys import argv
from ast import parse
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
        if self.get_reference_source() == "Unsat":
            return "Unsat"
        if self.reference_ast == None:
            self.reference_ast = parse(self.get_reference_source())
        for node in self.reference_ast.body:
            if FunctionLoader.is_template(node):
                return node

class SampleTester:
    
    def __init__(self, sample):
        self.sample = sample
    
    def run(self, syn = True, solve = True):
        if solve and self.sample.has_output():
            self.run_solve()
        if syn and self.sample.has_template():
            self.run_syn()


    def run_solve(self):
        ys = self.sample.get_output()
        try:
            indata=read_file_to_string(ys)
            indata_v=parse_vectors(indata)
            xs = solve_app(self.sample.get_source(), indata_v)
        except:
            print("Command solve failed on sample '%s'!" % self.sample.path)
            print_exc()
        else:
            # verify:
            f= FunctionExecutor(self.sample.get_ast(), 'f')
            
            for x, y in zip(xs, indata_v):
                if y != "Unsat":
                    y_ref=f.call(*x)
                    if y_ref is None:
                        y_ref=[]
                    elif not isinstance(y_ref,(tuple,list)):
                        y_ref=[y_ref]
                    else:
                        y_ref = list(y_ref)
                    if y_ref != y:
                        print "Incorrectly solved f(%s) = (%s) because f(%s) = (%s)!" % (
                            ", ".join(map(lambda a:str(a),x)),
                            ", ".join(map(lambda a:str(a),y)),
                            ", ".join(map(lambda a:str(a),x)),
                            ", ".join(map(lambda a:str(a),y_ref))
                            )
                # TODO: what about "Unsat"?
                
    def run_syn(self):
        try:
            actual = syn_app(self.sample.get_source())
        except:
            print("Command syn failed on sample '%s'!" % self.sample.path)
            print_exc()
        else:
            if not self.sample.has_reference():
                print("Syn yielded on sample '%s':" % self.sample.path)
                print(actual)
                return
            
            ref = self.sample.get_reference()

            if ref != "Unsat":
                ref = ast_to_source(ref)

            if actual == ref:
                return

            print("Synthesized solution differs from reference solution!")
            print("Reference Solution:")
            print(ref)
            print("")
            print("Synthesized Solution:")
            print(actual)
            print("")

        
if __name__ == "__main__":
    # ugly hack to collect .py files in sub directories
    if "--help" in argv:
        print("Usage: %s [--help] [--syn] [--solve] [list of test files]" % argv[0])
        print("   --help          Prints this help message and exits.")
        print("   --syn           Run at least 'syn' command on all specified test files.")
        print("   --solve         Run at least 'solve' command on all specified test files.")
        print("")
        print("                   If neither --syn nor --solve are given, then both")
        print("                   'syn' and 'solve' command are run on all specified")
        print("                   test files.")
        print("")
        print("   [list of files] If empty use all .py files in the samples folder")
        print("                   except for .ref.py files as specified test files.")
        print("                   Otherwise test on the list of files given.")
        exit()

    syn = "--syn" in argv
    solve = "--solve" in argv
    
    if syn:
        argv.remove("--syn")
    if solve:
        argv.remove("--solve")

    if not syn and not solve:
        syn = solve = True

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
        test.run(syn, solve)
        print("")
