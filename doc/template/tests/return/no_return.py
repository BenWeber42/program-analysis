# in this example f doesn't actually return


def f(x):
    x = 2*x
    x = x + 1000
    y = x


def f_inv(y):
    y = y - unknown_int() # should be 1000
    y = y/unknown_int() # should be 2
    x = y
    return x
