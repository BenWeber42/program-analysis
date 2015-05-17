# this testcase looks like it's reversible, but it's not

# this testcase is unfortunately only really interesting for the 'solve' command
# because detecting one exception suffices to yield 'Unsat' when it comes to 'syn'
# whereas we can make sure that all exceptions are detected correctly through
# giving different output values for the 'solve' command

def f(x1, x2):
    
    if x1 >= 750:
        # raises a ValueError
        x1, x2 = x1, x2, 5
        return x1, x2, 0

    if x1 >= 500:
        # raises a ValueError
        x1, x2, k = x1, x2
        return x1, x2, 1
    
    if x1 >= 250:
        # raises a NameError
        x1 = x1 + k
        return x1, x2, 2
    
    if x1 > 0:
        # clearly irreversible
        return 0, 0, 3
        return x1, x2, 3

    if x1 == 0:
        # raises ZeroDivisionError
        k = x1/x1
        return x1, x2, 4
    
    # the only reversible path
    return x1, x2, 5

def f_inv(y1, y2, y3):
    return unknown_choice(y1, y2, y3), unknown_choice(y1, y2, y3)