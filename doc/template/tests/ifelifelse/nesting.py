# this example has a lot of nested if/elif/else clauses, some are dead code


def f(x):
    if x >= 0:
        if x >= 500:
            return x*10 # x in [5000, 10000]
        elif x <= -200:
            return 5000 # deadcode
        elif x < 600: # always true
            return x # x in [0, 499]
        return 600 # deadcode
    if x >= -100:
        # here x in [-100, -1]
        if x <= -2:
            # here x in [-100, -2]
            if x == -5:
                return x*1000 # x = -5000
            else:
                if x == -6:
                    return x*1000 # x = -6000
    return x

def f_inv(y):
    if y >= 5000:
        return y/unknown_int() # should be 10
    if y >= -1000:
        if y >= 0:
            return unknown_choice(y, 0, 1000) # should be y
    if y == unknown_int(): # should be -5000
        return -5
    elif y == -6000:
        return unknown_int() # should be -6
    return y
