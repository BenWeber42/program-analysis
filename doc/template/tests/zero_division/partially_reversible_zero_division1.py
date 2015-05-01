# this example can contain a zero division, but is otherwise completely reversible

def f(x):
    if -3 <= x and x <= 3:
        return 1*2*3/x
    return x + 10000


def f_inv(y):
    if y < 10:
        return (1*2*3)/y
    return y - unknown_int() # should be 10000
