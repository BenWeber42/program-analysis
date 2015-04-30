# this testcase is technically not valid, but python's parser might hide this

def f(x):
    # this is the legacy != operator, it's not allowed per specification
    if x <> 0:
        return x + 10000
    return x


def f_inv(y):
    if y <> 0:
        return y - unknown_int() # should be 10000
    return y
