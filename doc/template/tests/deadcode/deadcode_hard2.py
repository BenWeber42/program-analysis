# this example uses a 'fairly' hard diophantin equation
# it has only solutions for x in [-15, 16] if we assume that x, y in [-1000, 1000]


def f(x, y):
    if not (-15 <= x and x <= 16):
        if x*x - x == y*y*y*y*y - y:
            return x, 10000
    return x, y


def f_inv(x, y):
    return x, unknown_choice(x, y, 10000) # should be y
