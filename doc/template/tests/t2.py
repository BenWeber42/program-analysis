
def f(a, b):
    if a + b == 0:
        return a, b
    return b, a

def f_inv(p, q):
    if p + q == 0:
        return unknown_choice(p,q), unknown_choice(p,q)
    return unknown_choice(p,q), unknown_choice(p,q)
