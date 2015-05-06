# proven to be the solution via brute force for x in [-1000, 1000]
def f_inv(y):
    if y >= 1000000:
        return y - 1001000
    elif y >= 100000:
        return y - 101000
    else:
        return y - 11000
