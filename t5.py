# this testcase requires careful handling of zero divisions when it comes to the template

def f(x,y):
    return x*y,x+440,y


def f_inv(p,x,y):
    dlt=unknown_choice(unknown_choice(y,2*unknown_int()),22)
    x2=unknown_choice(unknown_choice(x,unknown_choice(5*y)),2*x)

    if x2 == dlt:
        return x-unknown_int(),y
    return x-(100*unknown_int()+10*unknown_int()),unknown_choice(unknown_int(),p)/(x-unknown_int())

