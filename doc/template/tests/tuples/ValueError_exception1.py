# This function will raise a ValueError and thus can't be inverted

def f(x1, x2, x3, x4, x5):
    a, b, c = 1, 2 # this will raise a ValueError Exception!
    # thus we have to output 'Unsat'!
    return x1, x2, x3, x4, x4


def f_inv(y1, y2, y3, y4, y5):
    return y1, y2, y3, y4, y5
