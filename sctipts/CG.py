import numpy as np
import math
import sys
from math import sqrt
import numba
from numba import jit
from numba import int32, float32, int8, boolean

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
def direction(p, q, r):
    signed_area = ((q.x - p.x) * (r.y - p.y)) - ((q.y - p.y) * (r.x - p.x))

    if signed_area > 0:
        return 1
    elif signed_area < 0:
        return -1

    return 0

#@jit(nopython=True, parallel=True)
#@jit(int8(float32, float32, float32, float32, float32, float32))
#@jit(nopython=True)
def dir(px, py, qx, qy, rx, ry):
    signed_area = ((qx - px) * (ry - py)) - ((qy - py) * (rx - px))

    if signed_area > 0:
        return 1
    elif signed_area < 0:
        return -1

    return 0

@jit(int8(float32, float32, float32, float32, float32, float32))
def dir2(px, py, qx, qy, rx, ry):
    signed_area = ((qx - px) * (ry - py)) - ((qy - py) * (rx - px))

    if signed_area > 0:
        return 1
    elif signed_area < 0:
        return -1

    return 0

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
def distance(x1, y1, x2, y2):
    dx = x2 - x1
    dy = y2 - y1

    return sqrt(dx*dx + dy*dy)

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
def collinear(cp0, cp1, cp2, cp3, cp4, cp5, p0, p1):
    # Vertical line. All element travel in the same trajectory.
    if cp0.x == cp1.x and cp1.x == cp2.x and cp2.x == cp3.x and cp3.x == cp4.x and cp4.x == cp5.x and cp5.x == p0.x and p0.x == p1.x:
        return 1

    # Horizontal line. All element travel in the same trajectory.
    if cp0.y == cp1.y and cp1.y == cp2.y and cp2.y == cp3.y and cp3.y == cp4.y and cp4.y == cp5.y and cp5.y == p0.y and p0.y == p1.y:
        return 2

    dx = cp1.x - cp0.x
    dy = cp1.y - cp0.y

    if dx == 0:
        return 0

    m = dy / dx
    b = cp0.y - m * cp0.x

    # General line. All element travel in the same trajectory.
    if cp2.y == m * cp2.x + b and cp3.y == m * cp3.x + b and cp4.y == m * cp4.x + b and cp5.y == m * cp5.x + b and p0.y == m * p0.x + b and p1.y == m * p1.x + b:
        return 3

    # Generic case. Not all elements travel in the same trajectory.
    return 0

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
def left_index(coords):
    
    minn = 0
    
    for i in range(1, len(coords)): 
        if coords[i][0] < coords[minn][0]: 
            minn = i 
        elif coords[i][0] == coords[minn][0]: 
            if coords[i][1] > coords[minn][1]: 
                minn = i
    
    return minn
