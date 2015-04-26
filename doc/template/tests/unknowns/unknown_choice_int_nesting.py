# in this example an unknown_int is nested inside an unknown_choice, probably not valid

def f(x):
    return x + 30


def f_inv(y):
    return unknown_choice(y, y + 30, y + unknown_int())
