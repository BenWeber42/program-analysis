"""
Carries out several tests involving sample programs.
"""

from os import path
from pysyn import FunctionLoader, load_vectors, solve_app, compile_ast
from glob import glob
from traceback import print_exc

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
    
    # TODO: add functionality for the reference inverse function
    def has_ref_inverse(self):
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
   

class SampleTester:
    
    def __init__(self, sample):
        self.sample = sample
    
    def run(self):
        # TODO: syn
        if self.sample.has_output():

            ys = self.sample.get_output()
            try:
                xs = solve_app(self.sample.get_source(), ys)
            except:
                print("Command solve failed on sample '%s'!" % self.sample.path)
                print_exc()
                return
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
                

        # TODO: syn functionality
        
if __name__ == "__main__":
    # ugly hack to collect .py files in sub directories
    tests = glob("./samples/*.py")
    tests += glob("./samples/*/*.py")
    tests += glob("./samples/*/*/*.py")
    tests += glob("./samples/*/*/*/*.py")
    for f in tests:
        test = SampleTester(Sample(f))
        print(">>> Running testcase '%s'" % f)
        test.run()