#!/usr/bin/env python

from sys import argv
from pysyn import FunctionLoader, FunctionAnalyzer, PathDataGenerator
from math import ceil
import z3


def print_usage():
    print("Usage: %s [--help] [-n <X>] [file]" % argv[0])
    print("")
    print("   --help   prints this help message and exits.")
    print("")
    print("   -n <X>   Tries to generate at least X different testsets evenly distributed")
    print("            over the paths (default 1000)")
    print("")
    print("   [file]   Creates a dataset of output values that achieves 100% path coverage")
    print("            for a python function 'f' in [file].")
    print("")
    exit(0)


def generate(sample, n, at_least_one_per_path = True):

    f = FunctionLoader(sample).get_f()
        
    analyzer = FunctionAnalyzer(f)
    analyzer.analyze()
    
    paths = analyzer.paths
    
    if len(paths) == 0:
        print("Warning: No valid paths were found for sample '%s'!" % sample)
        return []
        
    per_path = int(ceil(float(n)/float(len(paths))))
    if at_least_one_per_path:
        per_path = max(per_path, 1)
    
    data = []
    
    for p in paths:
        data += PathDataGenerator(p).take(per_path)

    # TODO: generate Unsat samples too
	# Unfortunately that's not so straight forward
        
    return data


if __name__ == "__main__":
    if "--help" in argv:
        print_usage()
    
    n = 1000
    
    if "-n" in argv:
        index = argv.index("-n")
        
        if len(argv) <= index + 1:
            print_usage()
        
        n = str(argv[index + 1])
        argv = argv[:index] + argv[index + 2:]
    
    if len(argv) <= 1:
        print_usage()
    
    data = generate(argv[1], n)

    for v_in, v_out in data:
        print(" ".join(map(str, v_out)))