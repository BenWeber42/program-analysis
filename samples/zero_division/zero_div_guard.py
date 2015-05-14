# this example can contain a zero division, but is otherwise completely reversible

def f(x,y):
    return x*y,x+333,y


def f_inv(p,x,y):
    dlt=unknown_int()
    
    if p>100:
        if x == unknown_int():
            return x-dlt,y
        else:
            b=1
            return x-dlt,p/(x-dlt)
    else:
        if x == unknown_int():
            return x-unknown_int(),y
        return x-unknown_int(),p/(x-unknown_int())
    
