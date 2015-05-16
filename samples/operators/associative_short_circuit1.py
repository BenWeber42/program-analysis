# due to python's short circuit logic this function is reversible even if it contains a name error
# here it's important that pythons or operator must be left associative
# due to the short circuit logic
# therefore it's important to evaluate all terms to the left together

def f(x):
    if x >= 0 or x < 0 or x/0 == 8:
        return x
    return 10000


def f_inv(y):
    return unknown_choice(10000, y) # should be y