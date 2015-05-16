import unittest
from glob import glob
from datagenerator import generate, FunctionLoader
from pysyn import compile_ast


def execute_for_all(arguments):

    def decorator(old_method):
        
        def new_method(self):
            for arg in arguments:
                if arg.endswith("ref.py"):
                    continue
                old_method(self, arg)
        
        return new_method
    
    return decorator


class TestCorrectRelation(unittest.TestCase):
    
    num_data = 100
    
    samples = glob("../../samples/*.py")
    samples += glob("../../samples/*/*.py")
    samples += glob("../../samples/*/*/*.py")
    samples += glob("../../samples/*/*/*/*.py")
    
    samples += glob("../../samples_expensive/*.py")
    samples += glob("../../samples_expensive/*/*.py")
    samples += glob("../../samples_expensive/*/*/*.py")
    samples += glob("../../samples_expensive/*/*/*/*.py")

    @execute_for_all(samples)
    def testCorrectRelation(self, sample):
        
        print(">>> Running sample %s" % sample)
        
        data = generate(sample, self.num_data)
        
        f = compile_ast(FunctionLoader(sample).get_f())
        
        for v_in, v_out in data:

            actual_out = f(*v_in)
            
            if isinstance(actual_out, tuple):
                actual_out = list(actual_out)
            else:
                actual_out = [actual_out]
            
            self.assertEquals(actual_out, v_out,
                "In sample '" + sample + "' " +
                "actual f(" + ", ".join(map(str, v_in)) + ")" +
                " = (" + ", ".join(map(str, actual_out)) + ") " + 
                "but generated f(" + ", ".join(map(str, v_in)) + ")" +
                " = (" + ", ".join(map(str, v_out)) + ")!\n"
                )


if __name__ == "__main__":
    unittest.main()