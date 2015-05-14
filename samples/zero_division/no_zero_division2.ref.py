# proven correct by brute-force

def f_inv(y):
    if y > 2001:
        return (1*2*3*4*10000)/y - 1001
    else:
        return y - 1001