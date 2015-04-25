# this example contains deadcode that is easily detected


def f(x):
    if (x > 10000):
        return x/2
    return x


def f_inv(y):
    if (y > 3000):
        return unknown_int()*y # should be 2, but is deadcode
    return unknown_choice(y, 2, 0, 100) # should be y
