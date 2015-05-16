import unittest
from glob import glob
from pysyn import FunctionAnalyzer
from test import Sample

def execute_for_all(arguments):
    
    def decorator(old_method):
        
        def new_method(self):
            for arg in arguments:
                if arg.endswith("ref.py"):
                    continue
                old_method(self, arg)
        
        return new_method
    
    return decorator


class TestFunctionAnalyzer(unittest.TestCase):

    samples = glob("../../samples/*.py")
    samples += glob("../../samples/*/*.py")
    samples += glob("../../samples/*/*/*.py")
    samples += glob("../../samples/*/*/*/*.py")
    
    samples += glob("../../samples_expensive/*.py")
    samples += glob("../../samples_expensive/*/*.py")
    samples += glob("../../samples_expensive/*/*/*.py")
    samples += glob("../../samples_expensive/*/*/*/*.py")
    
    @execute_for_all(samples)
    def test_basics(self, name):
        
        print(">>> Running sample %s" % name)
        
        sample = Sample(name)
        
        analyzer = FunctionAnalyzer(sample.get_f())
        analyzer.analyze()
        
        if sample.has_reference():
            
            if analyzer.is_irreversible:
                self.assertTrue(sample.get_reference_source() == "Unsat",
                    "FunctionAnalyzer incorrectly classified sample '%s' as irreversible!" % name)
            
            if sample.get_reference_source() != "Unsat":
                self.assertTrue(len(analyzer.paths) >= 1,
                    "FunctionAnalyzer failed to find any path for reversible sample '%s'!" % name)
            
            if analyzer.is_irreversible or analyzer.migh_be_irreversible:
                self.assertTrue(len(analyzer.irreversible_path_constraints) >= 1,
                    "FunctionAnalzer didn't find any irreversible paths for sample '%s' yet classified it as possibly irreversible!" % name)


if __name__ == "__main__":
    unittest.main()