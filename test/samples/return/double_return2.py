#this example contains a trivial double return

def f(x):
    return x
    return 2*x + 10000


def f_inv(y):
    return unknown_choice(y, (y - 10000)/2) # should be y
