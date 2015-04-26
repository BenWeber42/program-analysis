# this example has unknown_choice nested, it's probably not valid

def f(x):
    return x


def f_inv(y):
    return unknown_choice(unknown_choice(y, y - 1, 3*y), 3*y/3, 0, unknown_choice(100, y))
