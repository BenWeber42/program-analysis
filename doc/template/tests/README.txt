Each test has some input (e.g. t1.inp), such that

./pysyn.py eval tests/t1.py tests/t2.inp

produces output. To test the solve, call:

./pysyn.py solve tests/t1.py tests/t2.out

it should produce the input (since the function f is a bijection).

Finally, the tests (except for t5.py) have f_inv to be synthesized.
