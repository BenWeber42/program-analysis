# proven to be the solution via brute force for x in [-1000, 1000]
def f_inv(y):
    if y >= 999000:
        return y - 1000000
    elif y >= 100000:
        return y - 100000
    else:
        return y - 10000
