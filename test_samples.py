"""
Carries out several tests involving sample programs.
"""

from os import path
from pysyn import FunctionLoader, load_vectors

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

        name, _ = path.splitext(p)

        self.input = name + ".inp"
        self.output = name + ".out"
        self.reference = name + ".syn.py"
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
        self.run = False
    
    def run(self):
        self.run = True
        # TODO
    
    def get_summary(self):
        assert self.run
        # TODO
    
    # TODO: get helper functions for statistics