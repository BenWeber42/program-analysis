# this example returns tuples of different lenghts and is therefore not valid


def f(x1, x2, x3):
    if x1 >= 0:
        return x1, x2, x3
    else:
        return x1, x2, x3, 10


def f_inv(y1, y2, y3):
    return unknown_choice(y1, y2, y3), unknown_choice(y1, y2, y3), unknown_choice(y1, y2, y3)
