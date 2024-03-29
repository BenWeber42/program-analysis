# this example tries to measure how well the solution deals with synthesization
# and solving

def f(x1, x2, x3):
    if  x1 == 0  or x2 == 0 or x3 == 0:
        return x1, x2, x3, 0
    if x1*x2 >= 30:
        return x1*x2*x3, x1*x2, x2*x3, 1
    else:
        return x1*x3,    x1*x2, x1*x2*x3, 1


def f_inv(y1, y2, y3, y4):
    if y4 == 0:
        return y1, y2, unknown_choice(y3, y2 + 50, y3 - 2)

    if unknown_choice(y2, y1, y4) >= 30:
        x1 = unknown_choice(y1/y3, y1/y2, y1/y1*5)
        x2 = y2/x1
        x3 = y3/x2
        return x1, x2, x3
    else:
        x2 = y3/y1
        x1 = y2/x2
        x3 = y1/x1
        return x1, x2, x3
