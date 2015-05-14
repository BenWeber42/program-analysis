# proven correct using 5 distinct argument values

def f_inv(y1, y2, y3, y4, y5):
    y1, y2, y3, y4, y5 = y2, y4, y5, y1, y3
    return y1, y2, y3, y4, y5