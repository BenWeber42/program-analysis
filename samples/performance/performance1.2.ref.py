# reference solution for all performance1.*.py examples

def f_inv(y1, y2, y3):
    if y1 >= 0:
        x1 = y1 + 0
        x2 = y3 - x1 - 30
        x3 = y2 - x2
        return x1, x2, x3
    else:
        x1 = y1
        x2 = (y2 - y3 - x1 - 10)/2
        x3 = y3 + (x2 - 30) + 30
        return x1, x2, x3