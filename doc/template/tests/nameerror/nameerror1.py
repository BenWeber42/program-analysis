# this example can raise a NameError exception and is therefore not reversibel


def f(x):
    if x >= 500:
        k = 10000
    return x + k


def f_inv(y):
    return y - unknown_int() # should be 10000, but the function isn't reversible
