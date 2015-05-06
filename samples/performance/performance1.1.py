# this example tries to measure how well the solution deals with synthesization
# and solving

def f(x1, x2, x3):
    if x1 >= 0:
        return x1, x2 + x3, x2 + x1 + 30
    else:
        return x1, 10 + x3 + x1 + x2, x3 - x2

def f_inv(y1, y2, y3):
    if y1 >= unknown_int():
        x1 = unknown_choice(y1, y3, 30)
        x2 = y3 - x1 - 5 + unknown_int()
        x3 = y2 - x2
        return x1, x2, x3
    else:
        x1 = y1
        x2 = (y2 - y3 - x1 - 10)/2
        x3 = y3 + unknown_choice(x2, y2, x1)
        return x1, x2, x3
