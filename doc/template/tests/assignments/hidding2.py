# this testcase uses assignments to hide previous values:


def f(x1, x2):
    x1 = x2 + x1
    x2 = 7*x2 + 5
    return x1, x2

def f_inv(y1, y2):
    x2 = (y2 - 5)/unknown_int() # should be 7
    x1 = y1 - unknown_choice(x2, y1, y2, 8) #should be x2
    return x1, x2
