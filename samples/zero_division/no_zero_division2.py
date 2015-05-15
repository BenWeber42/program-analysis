# it looks like it could contain a zero division, but it doesn't


def f(x):
    x = x + 1001 # here 1 <= x <= 2001
    if x <= 4:
        return (1*2*3*4*10000)/x
    else:
        return x

def f_inv(y):
    if y > 2001:
        return (1*2*3*4*10000)/unknown_choice(y, 0, 1, 2) - 1001 # should be y
    else:
        return y - unknown_int() # should be 1001
