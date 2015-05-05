# it looks like it could contain a zero division, but it doesn't


def f(x):
    if (x != 0):
        i = x/x
    else:
        i = 10000
    return x + i


def f_inv(y):
    if y == 10000:
        return unknown_choice(0, y) # should be 0
    else:
        return y - unknown_int() # should be 1
