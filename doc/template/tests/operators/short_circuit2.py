# due to python's short circuit logic this function is reversible even if it contains a division by zero


def f(x):
    if x > 5000 and x/0 == 8:
        return 10000
    return x


def f_inv(y):
    return unknown_choice(10000, y) # should be y
