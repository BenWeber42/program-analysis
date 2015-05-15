#!/usr/bin/env python

from sys import argv
from pysyn import FunctionLoader, FunctionAnalyzer


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