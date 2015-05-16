#!/usr/bin/env python

from sys import argv
from pysyn import FunctionLoader, FunctionAnalyzer, Path
from math import ceil
import z3


class PathDataGenerator:
    
    """
    Generates input/output samples for a given path
    """
    
    def __init__(self, path):
        self.path = path

        self.solver = z3.Solver()
        self.solver.add(path.constraints)
        self.solver.add(path.relation)
        self.solver.push()
        
        self.stack_size = 0
    
    
    def another(self):
        
        sat = self.solver.check()
        if sat != z3.sat:
            return None
    
        model = self.solver.model()

        in_vector = [model[x].as_long() for x in self.path.input]
        out_vector = [model[y].as_long() for y in self.path.output]

        # make sure we don't generate the same sample twice
        self.solver.add(z3.Not(z3.And(*[ x == model[x] for x in self.path.input])))
        self.solver.add(z3.Not(z3.And(*[ y == model[y] for y in self.path.output])))

        self.solver.push()
        self.stack_size += 1
        
        return (in_vector, out_vector)

    
    def take(self, num):
        v = []
        for i in xrange(num):
            d = self.another()

            if d == None:
                return v

            v.append(d)

        return v
    
    def reset(self):
        while self.stack_size > 0:
            self.solver.pop()
            self.stack_size -= 1


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