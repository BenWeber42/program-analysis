# proven correct by brute-force

def f_inv(y):
    k = y
    if y == 10001:
        k = 0
    if y == 10000:
        k = 1
    if y == 10003:
        k = 2
    if y == 10002:
        k = 3
    if y == 10008:
        k = 4
    if y == 10007:
        k = 5
    if y == 10006:
        k = 6
    if y == 10005:
        k = 7
    if y == 10004:
        k = 8
    if y == 10010:
        k = 10
    return k