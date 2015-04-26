# this example actually doesn't contain a NameError


def f(x):
    x = x + 1000 # now x is in [0, 2000]
    if x >= 500:
        k = 10000
    elif x >= 0:
        k = 100000
    else:
        k = 1000000
    return x + k


def f_inv(y):
    if y >= 1000000:
        return y - unknown_int() # should be 1000000
    elif y >= 100000:
        return y - unknown_int() # should be 100000
    else:
        return y - unknown_int() # should be 10000
