# this example contains many ifs, therefore many paths (paths scale exponentially with if clauses)


def f(x):
    k = x
    if x == 0:
        k = 10001
    if x == 2:
        k = 10003
    if x == 3:
        k = 10002
    if x == 8:
        k = 10004
    if x == 7:
        k = 10005
    if x == 6:
        k = 10006
    if x == 5:
        k = 10007
    if x == 4:
        k = 10008
    if x == 1:
        k = 10000
    if x == 10:
        k = 10010
    return k


def f_inv(y):
    k = y
    if y == 10001:
        k = unknown_int() # should be 0
    if y == 10000:
        k = unknown_int() # should be 1
    if y == unknown_int(): # should be 10003
        k = 2
    if y == unknown_int(): # should be 10002
        k = 3
    if y == 10008:
        k = unknown_int() # should be 4
    if y == unknown_int(): # should be 10007
        k = 5
    if y == 10006:
        k = unknown_int() # should be 6
    if y == unknown_int(): # should be 10005
        k = 7
    if y == unknown_int(): # should be 10004
        k = 8
    if y == unknown_int(): # should be 10010
        k = unknown_int() # should be 10
    return k
