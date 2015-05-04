"""
Carries out several tests involving sample programs.
"""

from os import path
import ast

class Sample:
    """
    Holds all information about a sample
    
    For a sample expects the following files:
    * <sample>.py - The sample program
    * <sample>.inp - The input vector if it exists
    * <sample>.out - The output vector if it exists
    * <sample>.syn.py - The synthesized inverse template function if it exists
    """

    def __init__(self, p):
        assert path.isfile(p)

        name, _ = path.splitext(p)

        self.sample = p
        self.input = name + ".inp"
        self.output = name + ".out"
        self.synthesized = name + ".syn.py"
        # they are used for lazy initialization
        self.source = None
        self.ast = None
        self.input_vectors = None
        self.output_vectors = None
        self.synthesized_ast = None
        self.synthesized_source = None
         
    def has_template(self):
        p = self.get_ast()
        for node in p.body:
            if Sample.is_template(node):
                return True
        return False
    
    def has_input(self):
        return path.isfile(self.input)
        
    def has_output(self):
        return path.isfile(self.output)
    
    def has_synthesized(self):
        return path.isfile(self.synthesized)
    
    def get_source(self):
        if self.source == None:
            self.source = Sample.get_content(self.sample)
        return self.source

    def get_ast(self):
        if self.ast == None:
            self.ast = ast.parse(self.get_source())
        return self.ast
   
    def get_f(self):
        p = self.get_ast()
        for node in p.body:
            if Sample.is_f(node):
                return node
  
    def get_template(self):
        assert self.has_template()
        p = self.get_ast()
        for node in p.body:
            if Sample.is_template(node):
                return node
                 
    def get_input(self):
        assert self.has_input()
        if self.input == None:
            self.input = Sample.load_vectors(self.input)
        return self.input

    def get_output(self):
        assert self.has_output()
        if self.output == None:
            self.output = Sample.load_vectors(self.output)
        return self.output

    @classmethod
    def is_f(cls, ast):
        return cls.is_function(ast, "f")
  
    @classmethod
    def is_template(cls, ast):
        return cls.is_function(ast, "f_inv")
   
    @classmethod
    def is_function(cls, ast, name):
        return type(ast).name == "FunctionDef" and ast.name == name
    
    @classmethod
    def get_content(cls, p):
        f = open(p, 'rt')
        s = f.read()
        f.close()
        return s
    
    @classmethod
    def load_vectors(cls, p):
        return Sample.parse_vectors(Sample.get_content(p))

    @classmethod
    def parse_vectors(cls, s):
        return [ map(lambda x: x if x == "Unsat" else int(x), vec.split(" ")) for vec in s.split("\n") if vec != '']

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