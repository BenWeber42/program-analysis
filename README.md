# Program Analysis Project

In this project, for a given python function `f` we had to solve two tasks:

1) Given `y` such that `y = f(x)`, find `x` (reverting `f`).
2) Given `f` and a template with missing parts for an inverse function `f_inv`, fill out the missing parts.

The function `f` only consisted of a subset of python (no loops or recursion, so no turing completeness).
We had to use z3 to solve this task.

Our approach can be found in `pysyn.py`.
