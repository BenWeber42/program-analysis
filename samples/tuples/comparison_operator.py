# This is probably not part of the valid python subset


def f(x1, x2, x3, x4, x5):
    if (x1, x2, x3, x4, x5) == (x1, x3, x4, x4, x5):
        x1 = x1 + 5
    x1, x2, x3, x4, x4 = x3, x5, x1, x2, x4
    return x1, x2, x3, x4, x4


def f_inv(y1, y2, y3, y4, y5):
    y1, y2, y3, y4, y5 = unknown_choice(y1, y2, y3, y4, y5), unknown_choice(y1, y2, y3, y4, y5), unknown_choice(y1, y2, y3, y4, y5), unknown_choice(y1, y2, y3, y4, y5), unknown_choice(y1, y2, y3, y4, y5)
    return y1, y2, y3, y4, y5
