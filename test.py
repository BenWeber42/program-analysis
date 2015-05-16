#!/usr/bin/env python
"""
Carries out several tests involving sample programs.
"""

from signal import signal, SIGSEGV
from glob import glob
from traceback import print_exc, print_stack
from sys import argv
from ast import parse
from pysyn import *
from random import randint

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
        if self.get_reference_source().replace("\n", "") == "Unsat":
            return "Unsat"
        if self.reference_ast == None:
            self.reference_ast = parse(self.get_reference_source())
        for node in self.reference_ast.body:
            if FunctionLoader.is_template(node):
                return node


def generate_output_space(f, num_args):
    
    assert(1 <= num_args and num_args <= 2)
    
    ys = set()
    for x1 in xrange(-1000, 1001):
        if num_args == 1:
            try:
                y = f(x1)
            except:
                pass
            else:
                ys.add(y)
        else:
            for x2 in xrange(-1000, 1001):
                try:
                    y = f((x1, x2))
                except:
                    pass
                else:
                    ys.add(y)
    
    return ys


class SampleTester:
    
    def __init__(self, sample):
        self.sample = sample
    
    def run(self, syn = True, solve = True):
        if solve and self.sample.has_output():
            self.run_solve()
        if syn and self.sample.has_template():
            self.run_syn()


    def run_solve(self):

        ys = load_vectors(self.sample.get_output())

        try:
            xs = solve_app(self.sample.get_f(), ys)
        except:
            print("Command solve failed on sample '%s'!" % self.sample.path)
            print_exc()
        else:

            if len(xs) != len(ys):
                print("Solve didn't output enough input data!")

            # verify:
            f = compile_ast(self.sample.get_f())
            
            if len(self.sample.get_f().args.args) <= 2:
                # for such a small parameter space it's ok to use a brute-force approach
                valid_y = generate_output_space(f, len(self.sample.get_f().args.args))
            else:
                # TODO: find a good way to check 'Unsat' for bigger parameter space
                valid_y = set()

            for x, y in zip(xs, ys):
                if x != ["Unsat"]:

                    try:
                        y_actual = f(*x)
                    except:
                        print "Incorrectly solved f(%s) = (%s) because f(%s) raises an exception!" % (
                            ", ".join(map(str, x)),
                            ", ".join(map(str, y)),
                            ", ".join(map(str, x))
                            )
                        break

                    if isinstance(y_actual, tuple):
                        y_actual = list(y_actual)
                    else:
                        y_actual = [y_actual]

                    if y_actual != y:
                        print "Incorrectly solved f(%s) = (%s) because f(%s) = (%s)!" % (
                            ", ".join(map(str, x)),
                            ", ".join(map(str, y)),
                            ", ".join(map(str, x)),
                            ", ".join(map(str, y_actual))
                            )
                        break

                else:
                    if isinstance(y, list):
                        y = tuple(y)

                    if y in valid_y:
                        # Note: We just need to find any x such that f(x) = y
                        # so it's not a problem if there exists x1 != x1 with f(x1) = f(x2) = y
                        print("Incorrectly yielded 'Unsat' because (%s) is part of f's output space!" %
                              ", ".join(map(str, y)))
                        break


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
                
                if actual != "Unsat":
                    f = FunctionExecutor(ast.parse(self.sample.get_source()), 'f', {})
                    f_inv = FunctionExecutor(ast.parse(actual), 'f_inv', {})

                    for i in range(1000):                
                        a = []
                        for i in range(len(f.spec.args)):
                            a.append(randint(-1000, 1000));
                        res = f.call(*a)
                        if isinstance(res, tuple):
                            b = f_inv.call(*res)
                        else:
                            b = f_inv.call(res)
                    
                        if isinstance(b, tuple):
                            b = list(b)
                        else:
                            b = [b]

                        if a != b:
                            print("Difference for args: in " + str(a) + " out inv " + str(b))
                            break

            if actual == ref:
                return

            print("Synthesized solution differs from reference solution!")
            print("Reference Solution:")
            print(ref)
            print("")
            print("Synthesized Solution:")
            print(actual)
            print("")


def segfault_handler(signum, frame):
    print("Segfault!!!")

    if frame != None:
        print_stack(frame)
    else:
        print("frame == None")

    exit()
        
if __name__ == "__main__":
    
    #signal(SIGSEGV, segfault_handler)

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
        tests += glob("./samples_expensive/*.py")
        tests += glob("./samples_expensive/*/*.py")
        tests += glob("./samples_expensive/*/*/*.py")
        tests += glob("./samples_expensive/*/*/*/*.py")
    else:
        tests = argv[1:]

    for f in tests:
        # ignore reference solutions
        if f.endswith("ref.py"):
            continue
        print(">>> Running testcase '%s'" % f)
        test = SampleTester(Sample(f))
        test.run(syn, solve)
        print("")
