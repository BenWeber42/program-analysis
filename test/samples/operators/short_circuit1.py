# due to python's short circuit logic this function is reversible even if it contains a name error

def f(x):
    if x > -5000 or k == 8:
        return x
    return 10000


def f_inv(y):
    return unknown_choice(10000, y) # should be y
