# reference solution for all performance2.*.py examples

def f_inv(y1, y2, y3, y4):
    if y4 == 0:
        return y1, y2, y3

    if y2 >= 30:
        x1 = y1/y3
        x2 = y2/x1
        x3 = y3/x2
        return x1, x2, x3
    else:
        x2 = y3/y1
        x1 = y2/x2
        x3 = y1/x1
        return x1, x2, x3
