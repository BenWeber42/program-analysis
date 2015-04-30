
def f(x1, x2):
    x1, x2 = x2, x1
    return x1, x2


def f_inv(y1, y2):
    y1, y2 = unknown_choice(y1, y2), unknown_choice(y1, y2)
    return y1, y2