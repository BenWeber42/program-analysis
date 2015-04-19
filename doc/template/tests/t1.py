
def f(x, y):
    return (2+x, 12+x+y)

def f_inv(u, v):
    a = unknown_choice(u,v,0,-u,-v) + unknown_choice(u,v,0,-u,-v) + unknown_int()
    b = unknown_choice(u,v,0,-u,-v) + unknown_choice(u,v,0,-u,-v) + unknown_int()
    return a, b
