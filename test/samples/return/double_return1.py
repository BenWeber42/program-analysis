# this example contains double returns

def f(x):
    if x == 0:
        return 10001
    else:
        return x
    return 10002


def f_inv(y):
    if y == unknown_int(): # should be 10001
        return 0
    if y == 10002:
        return unknown_int() # dead code, so could be anything
    return unknown_choice(y, 10001, 10002, 0) # should be y
