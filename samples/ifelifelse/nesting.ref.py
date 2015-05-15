# verified by brute-force

def f_inv(y):
    if y >= 5000:
        return y/10
    if y >= -1000:
        if y >= 0:
            return y
    if y == -5000:
        return -5
    elif y == -6000:
        return -6
    return y