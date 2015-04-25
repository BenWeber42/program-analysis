# this testcase uses assignments to hide previous values:


def f(x):
    x = x + 1
    x = x*x
    x = 2*x - 3 + 5*x
    return x

def f_inv(y):
    y = unknown_int()*unknown_choice(y, y*y) + unknown_int()*y + unknown_int()
    return y
