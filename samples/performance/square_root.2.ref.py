# using a binary search to calculate the square root
# using bruteforce we've shown that f_inv(*f(x)) = x for x in [-1000, 1000]
def f_inv(y1, y2):

    lower = 0
    upper = 1001

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    mid = (lower + upper)/2

    if mid*mid <= y1:
        lower = mid
    else:
        upper = mid

    x = (lower + upper)/2

    if y2 == 0:
        return +x
    return -x
