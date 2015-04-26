# in this example the f_inv function returns tuples of different lenghts


def f(x1, x2, x3):
    if x1 >= 0:
        return x1, x2, x3, 100
    else:
        return x3, x2, x1, 0


def f_inv(y1, y2, y3, y4):
    if y4 == 100:
        return y1, y2, y3
    else:
        return unknown_choice(y1, y2, y3, y4), unknown_choice(y1, y2, y3, y4), unknown_choice(y1, y2, y3, y4), 0
