# this example has no else clause


def f(x):
    if x == 100:
        return x + 10000
    elif x == 101:
        return x + 100000
    return x


def f_inv(y):
    if y == 100101:
        return unknown_int() # should be 101
    elif y == unknown_int(): # should be 10100
        return 100
    return y
