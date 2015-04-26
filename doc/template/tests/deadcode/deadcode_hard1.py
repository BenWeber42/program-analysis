# this example makes use of fermat's theorem, thus it's much harder to detect the deadcode
# fermat's theorem states that there are no three positive integers a, b, c such that a^n + b^n = c^n for n > 2
# this was only proven in 1994


def f(a, b, c):
    if a > 0 and b > 0 and c > 0:
        if a*a*a + b*b*b == c*c*c:
            return a, b, c + 3000
        return a, b, c
    return a, b, c


def f_inv(a, b, c):
    return a, b, unknown_choice(a, b, c) # should be c
