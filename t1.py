# this testcase looks like it's irreversible, but it's reversible


def f(x1, x2, x3):

    # this is about fermat's theorem
    # in 1994 it was finally proven
    # so since then we know this is deadcode (for all x1, x2, x3 > 0)
    if x1 > 0 and x2 > 0 and x3 > 0:
        if x1*x1*x1 + x2*x2*x2 == x3*x3*x3:
            # deadcode

            # would raise a ValueError
            x1, x2 = x1, x2, x3
            # would raise a ValueError
            x1, x2, x3 = x1, x2
            # would raise a ZeroDivisionError
            x1 = x1/0
            # would raise a NameError
            x1 = x1 + k
            # would make it irreversible
            return 0, 0, 0
    

    # this is a hard diophantin equation that only has solutions for
    # x in [-15, 16] given that x, y in [-1000, 1000]
    if not (-15 <= x1 and x1 <= 16):
        if x1*x1 - x1 == x2*x2*x2*x2*x2 - x2:
            # deadcode

            # would raise a ValueError
            x1, x2 = x1, x2, x3
            # would raise a ValueError
            x1, x2, x3 = x1, x2
            # would raise a ZeroDivisionError
            x1 = x1/0
            # would raise a NameError
            x1 = x1 + k
            # would make it irreversible
            return 0, 0, 0
    

    # due to python's short-circuit logic this won't raise an exception
    if x1 > 5000 and x1/0 == 8 and k == 0:
        # deadcode

        # would raise a ValueError
        x1, x2 = x1, x2, x3
        # would raise a ValueError
        x1, x2, x3 = x1, x2
        # would raise a ZeroDivisionError
        x1 = x1/0
        # would raise a NameError
        x1 = x1 + k
        # would make it irreversible
        return 0, 0, 0
        
    # due to python's short-circuit logic this won't rais an exception
    if not (x1 > -5000 or k == 8 and x1/0 == 8):
        # deadcode

        # would raise a ValueError
        x1, x2 = x1, x2, x3
        # would raise a ValueError
        x1, x2, x3 = x1, x2
        # would raise a ZeroDivisionError
        x1 = x1/0
        # would raise a NameError
        x1 = x1 + k
        # would make it irreversible
        return 0, 0, 0

    # a special case of python's short-circuit logic that will avoid exceptions
    if not (x1 >= 0 or x1 < 0 or x1/0 == 8 or k == 0):
        # deadcode

        # would raise a ValueError
        x1, x2 = x1, x2, x3
        # would raise a ValueError
        x1, x2, x3 = x1, x2
        # would raise a ZeroDivisionError
        x1 = x1/0
        # would raise a NameError
        x1 = x1 + k
        # would make it irreversible
        return 0, 0, 0
    
    # a special case of python's short-circuit logic that will avoid exceptions
    if x1 == 0 and x1 == 1 and x1/0 == 8 or k == 3:
        # deadcode

        # would raise a ValueError
        x1, x2 = x1, x2, x3
        # would raise a ValueError
        x1, x2, x3 = x1, x2
        # would raise a ZeroDivisionError
        x1 = x1/0
        # would raise a NameError
        x1 = x1 + k
        # would make it irreversible
        return 0, 0, 0
    

    return x1, x2, x3


def f_inv(y1, y2, y3):
    # should be return y1, y2, y3
    return unknown_choice(y1, y2, y3), unknown_choice(y1, y2, y3), unknown_choice(y1, y2, y3)