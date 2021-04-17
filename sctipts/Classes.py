#import numpy as np
from shapely.geometry import Point, Polygon, LineString, MultiPolygon
#import shapely.wkt
#from shapely.wkt import dumps, loads
import math
import sys
from CG import direction, dir, distance
import numba
from numba import int32, float32, boolean
from numba import jitclass

point_spec = [
    ('x', float32),               # a simple scalar field
    ('y', float32),               # a simple scalar field
]

#@jitclass(point_spec)
class Point:

    def __init__(self, x, y):
        self.x = x
        self.y = y

    def to_string(self):
        return "POINT (" + str(self.x) + ", " + str(self.y) + ")"

int_spec = [
    ('x', float32),
    ('y', float32),
    ('l', boolean),
    ('r', boolean),
    ('valid', boolean)
]

#@jitclass(int_spec)
class Interval:

    def __init__(self, x, y, l, r):
        self.x = x
        self.y = y
        self.l = l
        self.r = r
        self.valid = True

        if self.y <= self.x:
            self.valid = False

    def begin(self):
        return self.x

    def end(self):
        return self.y

    # TODO: Use t <= y or t < y
    def contains(self, t):
        return self.x <= t and t <= self.y

    def contains_strict(self, t):
        return (self.x < t and t < self.y) or (t == self.x and self.l) or (t == self.y and self.r)

    def contains_left(self, t):
        return (self.x < t and t < self.y) or (t == self.x and self.l)

    def contains_right(self, t):
        return (self.x < t and t < self.y) or (t == self.y and self.r)

    def intersects(self, i):
        if not self.valid or not i.valid:
            return None

        return not (self.y <= i.x or i.y <= self.x)

    def intersection(self, i):
        # TODO: Intersection can be an instant! Check this.
        if not self.valid or not i.valid:
            return None

        if not self.intersects(i):
            return None

        nb = self.x
        ne = self.y

        if i.x > nb:
            nb = i.x;

        if i.y < ne:
            ne = i.y;

        if nb == ne:
            return nb

        nl = self.contains_left(nb) and i.contains_left(nb)
        nr = self.contains_right(ne) and i.contains_right(ne)

        return Interval(nb, ne, nl, nr)

    def equals(self, other):
        return self.x == other.begin() and self.y == other.end()

    def to_string(self):
        s = "INTERVAL "

        if self.l:
            s += "["
        else:
            s += "]"
        
        s += str(self.x) + ", " + str(self.y)

        if self.r:
            s += "]"
        else:
            s += "["
        return s

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
class QuadBezierCurve:
    def __init__(self, cp0, cp1, cp2):
        self.cp0 = cp0
        self.cp1 = cp1
        self.cp2 = cp2

        self.cp1x = 2 * self.cp1.x
        self.cp1y = 2 * self.cp1.y

        x, y = self.at(0.5)
        middle_point = Point(x, y)

        if direction(self.cp0, self.cp2, middle_point) == 0:
            self.degenerated_to_linear = True
        else:
            self.degenerated_to_linear = False

    def at(self, t):
        mt  = 1-t
        mt2 = mt*mt
        mtt = mt*t
        t2  = t*t

        #print(mt, mt2, mtt, t2, t)

        #print(self.cp0.x, self.cp1x, self.cp2.x)

        #Ax = self.cp0.x * mt2 + 2 * self.cp1.x * mtt + self.cp2.x * t2
        #Ay = self.cp0.y * mt2 + 2 * self.cp1.y * mtt + self.cp2.y * t2
        Ax = self.cp0.x * mt2 + self.cp1x * mtt + self.cp2.x * t2
        Ay = self.cp0.y * mt2 + self.cp1y * mtt + self.cp2.y * t2

        return Ax, Ay

    def wkt_at(self, t):
        Ax, Ay = self.at(t)
        return 'LINESTRING (' + str(Ax) + ' ' + str(Ay) + ', ' + str(Ax) + ' ' + str(Ay) + ')'

    def to_string(self):
        return "QBC: cp0: " + self.cp0.to_string() + ", cp1: " + self.cp1.to_string() + ", cp2: " + self.cp2.to_string()

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
class CCurve:

    def __init__(self):
        self.curves = []
        self.intervals = []

    def add_curve(self, c, i):
        self.curves += [c]
        self.intervals += [i]

    def at(self, t):
        k = 0
        idx = 0
        n = len(self.intervals)

        while idx < n:
            if self.intervals[idx].contains(t):
                break

            idx += 1

        if idx >= n:
            print_error(-21, 'Invalid instant!')

        i = self.intervals[idx]
        c = self.curves[idx]

        dt = i.y - i.x
        t = (t - i.x) / dt

        return c.at(t)

    def to_string(self):
        s = "["
        n = len(self.curves)
        idx = 0

        while idx < n:
            if idx > 0:
                s += ", "

            s += "<" + self.curves[idx].to_string() + ", i: " + self.intervals[idx].to_string() + ">"
            idx += 1

        return s + "]"

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
class MSU:

    def __init__(self, c0, c1, i):
        self.c0 = c0
        self.c1 = c1
        self.mbb = []
        self.i = i

        c = self.c0.curves[0]
        
        x1 = c.cp0.x
        y1 = c.cp0.y

        x2 = c.cp1.x
        y2 = c.cp1.y

        x3 = c.cp2.x
        y3 = c.cp2.y

        m0, b0 = f(x1, y1, x3, y3)
        mp, bp = f_p(x2, y2, m0)

        c = self.c1.curves[0]
        
        x4 = c.cp0.x
        y4 = c.cp0.y

        x5 = c.cp1.x
        y5 = c.cp1.y

        x6 = c.cp2.x
        y6 = c.cp2.y

        m1, b1 = f(x4, y4, x6, y6)
        mp1, bp1 = f_p(x5, y5, m1)

        ma, ba = f(x1, y1, x4, y4)
        mb, bb = f(x3, y3, x6, y6)

        xa, ya = fi(ma, ba, mp, bp)
        xb, yb = fi(mb, bb, mp, bp)

        xc, yc = fi(ma, ba, mp1, bp1)
        xd, yd = fi(mb, bb, mp1, bp1)

        d1 = distance(x1, y1, x4, y4)
        d2 = distance(xa, ya, x4, y4)

        self.min1 = None
        self.max1 = None

        self.min2 = None
        self.max2 = None

        if d1 < d2:
            self.min1 = (x1, y1, x3, y3)
            self.max1 = (xa, ya, xb, yb)
        else:
            self.max1 = (x1, y1, x3, y3)
            self.min1 = (xa, ya, xb, yb)

        d2 = distance(xc, yc, x1, y1)

        if d1 < d2:
            self.min2 = (x4, y4, x6, y6)
            self.max2 = (xc, yc, xd, yd)
        else:
            self.max2 = (x4, y4, x6, y6)
            self.min2 = (xc, yc, xd, yd)

        minx = min(min(self.max1[0], self.max1[2]), min(self.max2[0], self.max2[2]))
        miny = min(min(self.max1[1], self.max1[3]), min(self.max2[1], self.max2[3]))
        maxx = max(max(self.max1[0], self.max1[2]), max(self.max2[0], self.max2[2]))
        maxy = max(max(self.max1[1], self.max1[3]), max(self.max2[1], self.max2[3]))

        self.bb = (minx, miny, maxx, maxy)

        self.left = minx
        self.right = maxx
        self.top = maxy
        self.bottom = miny

    def atop(self, t, max = 1):
        if max == 1:
            dx = self.max1[2] - self.max1[0]
            dy = self.max1[3] - self.max1[1]

            Ax = self.max1[0] + dx * t
            Ay = self.max1[1] + dy * t

            dx = self.max2[2] - self.max2[0]
            dy = self.max2[3] - self.max2[1]

            Bx = self.max2[0] + dx * t
            By = self.max2[1] + dy * t
        else:
            dx = self.min1[2] - self.min1[0]
            dy = self.min1[3] - self.min1[1]

            Ax = self.min1[0] + dx * t
            Ay = self.min1[1] + dy * t

            dx = self.min2[2] - self.min2[0]
            dy = self.min2[3] - self.min2[1]

            Bx = self.min2[0] + dx * t
            By = self.min2[1] + dy * t

        return Ax, Ay, Bx, By

    def atop2(self, max = 1):
        if max == 1:
            b = self.max1[2] - self.max1[0]
            d = self.max1[3] - self.max1[1]

            a = self.max1[0]
            c = self.max1[1]

            f = self.max2[2] - self.max2[0]
            h = self.max2[3] - self.max2[1]

            o = self.max2[0]
            g = self.max2[1]
        else:
            b = self.min1[2] - self.min1[0]
            d = self.min1[3] - self.min1[1]

            a = self.min1[0]
            c = self.min1[1]

            f = self.min2[2] - self.min2[0]
            h = self.min2[3] - self.min2[1]

            o = self.min2[0]
            g = self.min2[1]

        return a, b, c, d, o, f, g, h

    def at(self, t):
        Ax, Ay = self.c0.at(t)
        Bx, By = self.c1.at(t)

        return Ax, Ay, Bx, By

    def at_0(self, t):
        Ax, Ay = self.c0.at(t)

        return Ax, Ay

    def at_1(self, t):
        Bx, By = self.c1.at(t)

        return Bx, By

    def wkt_at(self, t):
        Ax, Ay, Bx, By = self.at(t)
        return 'LINESTRING (' + str(Ax) + ' ' + str(Ay) + ', ' + str(Bx) + ' ' + str(By) + ')'

    def obj_at(self, t):
        Ax, Ay, Bx, By = self.at(t)
        return LineString([(Ax, Ay), (Bx, By)])

    def to_string(self):
        return "MSU: c0: " + self.c0.to_string() + ", c1: " + self.c1.to_string() + ", i: " + self.i.to_string()

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
class MovingSegment:

    def __init__(self):
        self.units = []

    def add_unit(self, unit):
        self.units += [unit]

    def at(self, t):
        # General solution assuming non-constant sampling.
        idx = 0
        n = len(self.units)

        while idx < n:
            if self.units[idx].i.contains(t):
                return self.units[idx].at(t)

            idx += 1

        return None, None, None, None

    def wkt_at(self, t):
        # General solution assuming non-constant sampling.
        idx = 0
        n = len(self.units)

        while idx < n:
            if self.units[idx].i.contains(t):
                return self.units[idx].wkt_at(t)

            idx += 1

        return 'LINESTRING EMPTY'

    def obj_at(self, t):
        # General solution assuming non-constant sampling.
        idx = 0
        n = len(self.units)

        while idx < n:
            if self.units[idx].i.contains(t):
                return self.units[idx].obj_at(t)

            idx += 1

        return None

    def on(self, t, Px, Py):
        # Need to implement this.
        pass

    def to_string(self):
        s = "MS: ["
        idx = 0
        n = len(self.units)

        while idx < n:
            if idx > 0:
                s += ", "

            s += self.units[idx].to_string()
            idx += 1

        s += "]"
        return s

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
class MPU:

    def __init__(self, p, i):
        self.p = p
        self.i = i

        if len(p) != 2:
            print("Invalid moving point params!")
            sys.exit()

    def at(self, t):
        dx = self.p[1].x - self.p[0].x
        dy = self.p[1].y - self.p[0].y

        Px = self.p[0].x + dx * t
        Py = self.p[0].y + dy * t
        
        return Px, Py

    def wkt_at(self, t):
        Px, Py = self.at(t)
        return 'LINESTRING (' + str(Px) + ' ' + str(Py) + ', ' + str(Px) + ' ' + str(Py) + ')'

    def to_string(self):
        return "MPU: p0: " + self.p[0].to_string() + ", p1: " + self.p[1].to_string() + ", i: " + self.i.to_string()

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
class MovingPoint:

    def __init__(self):
        self.units = []

    def add_unit(self, unit):
        self.units += [unit]

    def at(self, t):
        idx = 0
        n = len(self.units)

        while idx < n:
            if self.units[idx].i.contains(t):
                dt = self.units[idx].i.y - self.units[idx].i.x
                t = (t - self.units[idx].i.x) / dt
                return self.units[idx].at(t)

            idx += 1

        return None, None

    def wkt_at(self, t):
        # General solution assuming non-constant sampling.
        idx = 0
        n = len(self.units)

        while idx < n:
            if self.units[idx].i.contains(t):
                dt = self.units[idx].i.y - self.units[idx].i.x
                t = (t - self.units[idx].i.x) / dt
                return self.units[idx].wkt_at(t)

            idx += 1

        return 'LINESTRING EMPTY'

    def to_string(self):
        s = "MP: ["
        idx = 0
        n = len(self.units)

        while idx < n:
            if idx > 0:
                s += ", "

            s += self.units[idx].to_string()
            idx += 1

        s += "]"
        return s

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
def f(x1, y1, x2, y2):
    dx = x2 - x1
    dy = y2 - y1

    m = None
    b = None

    if dx == 0:
        b = x1
    else:
        m = dy / dx
        b = y1 - m * x1

    return m, b

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
def fi(m1, b1, m2, b2):
    if m1 == None:
        x = b1
        y = m2 * x + b2
    elif m2 == None:
        x = b2
        y = m1 * x + b1
    else:
        x = (b2 - b1) / (m1 - m2)
        y = m1 * x + b1

    return x, y

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
def f_p(x, y, m):
    if m == None:
        b = x
    else:
        b = -(m * x) + y

    return m, b

