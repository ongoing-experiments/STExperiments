#-------------------------------------------------------------------
# Imports.
#-------------------------------------------------------------------

#from numba import jit
import collections
import os
import random
import time
import enum
from sympy import re, im
import numpy as np
from shapely.geometry import Point, Polygon, LineString, MultiPolygon, MultiLineString, GeometryCollection
import shapely.wkt
from shapely.wkt import dumps, loads
import math
from MSeg import MSeg
import sys
import Seg
import math
from math import atan
from Utils import distance

#M_PI = 3.14159265358979323846
#M_PI_OVER_2 = M_PI / 2

class Operation(enum.Enum): 
    Intersects = 1
    Touches = 2
    Equals = 3
    Disjoint = 4
    Contains = 5
    Within = 6
    Crosses = 7
    Overlaps = 8

class State(enum.Enum): 
    Intersect = 1
    Touch = 2
    Disjoint = 3
    Inside = 4

#-------------------------------------------------------------------
# Classes
#-------------------------------------------------------------------

class Point:

    def __init__(self, x, y):
        self.x = x
        self.y = y

    def to_string(self):
        return "POINT (" + str(self.x) + ", " + str(self.y) + ")"

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
        """
        if nb == self.x:
            nl = self.l
        elif nb == i.x:
            nl = i.l
        """
        nr = self.contains_right(ne) and i.contains_right(ne)
        """
        if ne == self.y:
            nr = self.r
        elif ne == i.y:
            nr = i.r
        """
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

class QuadBezierCurve:

    def __init__(self, cp0, cp1, cp2):
        self.cp0 = cp0
        self.cp1 = cp1
        self.cp2 = cp2

        x, y = self.at(0.5)
        middle_point = Point(x, y)

        if direction(self.cp0, self.cp2, middle_point) == 0:
            self.degenerated_to_linear = True
        else:
            self.degenerated_to_linear = False

    def at(self, t):
        mt  = (1 - t)
        mt2 = mt ** 2
        mtt = mt * t
        t2  = t ** 2

        Ax = self.cp0.x * mt2 + 2 * self.cp1.x * mtt + self.cp2.x * t2
        Ay = self.cp0.y * mt2 + 2 * self.cp1.y * mtt + self.cp2.y * t2

        return Ax, Ay

    def wkt_at(self, t):
        Ax, Ay = self.at(t)
        return 'LINESTRING (' + str(Ax) + ' ' + str(Ay) + ', ' + str(Ax) + ' ' + str(Ay) + ')'

    def to_string(self):
        return "QBC: cp0: " + self.cp0.to_string() + ", cp1: " + self.cp1.to_string() + ", cp2: " + self.cp2.to_string()

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
            #print(self.intervals[idx].to_string())
            if self.intervals[idx].contains(t):
                break

            idx += 1

        if idx >= n:
            print("ERR: Invalid instant?", idx, n, t)
            sys.exit()

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

class MSU:

    def __init__(self, c0, c1, i):
        self.c0 = c0
        self.c1 = c1
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

        #self.bb = (minx, miny, maxx, maxy)

        self.left = minx
        self.right = maxx
        self.top = maxy
        self.bottom = miny

    def at(self, t):
        Ax, Ay = self.c0.at(t)
        Bx, By = self.c1.at(t)

        return Ax, Ay, Bx, By

    def wkt_at(self, t):
        Ax, Ay, Bx, By = self.at(t)
        return 'LINESTRING (' + str(Ax) + ' ' + str(Ay) + ', ' + str(Bx) + ' ' + str(By) + ')'

    def obj_at(self, t):
        Ax, Ay, Bx, By = self.at(t)
        return LineString([(Ax, Ay), (Bx, By)])

    def to_string(self):
        return "MSU: c0: " + self.c0.to_string() + ", c1: " + self.c1.to_string() + ", i: " + self.i.to_string()

class MPU2:

    def __init__(self, c, i):
        self.c = c
        self.i = i

        c = self.c.curves[0]

        x1 = c.cp0.x
        y1 = c.cp0.y

        x2 = c.cp1.x
        y2 = c.cp1.y

        x3 = c.cp2.x
        y3 = c.cp2.y

        minx = min(min(x1, x2), x3)
        miny = min(min(y1, y2), y3)
        maxx = max(max(x1, x2), x3)
        maxy = max(max(y1, y2), y3)

        self.left = minx
        self.right = maxx
        self.top = maxy
        self.bottom = miny

    def at(self, t):
        Ax, Ay = self.c.at(t)

        return Ax, Ay

    def wkt_at(self, t):
        Ax, Ay = self.c.at(t)
        return 'LINESTRING (' + str(Ax) + ' ' + str(Ay) + ', ' + str(Ax) + ' ' + str(Ay) + ')'

    def obj_at(self, t):
        Ax, Ay = self.c.at(t)
        return LineString([(Ax, Ay), (Ax, Ay)])

    def to_string(self):
        return "MSU2: c: " + self.c.to_string() + ", i: " + self.i.to_string()

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
                if isinstance(self.units[idx], MPU2):
                    return self.units[idx].at(t)
                else:
                    dt = self.units[idx].i.y - self.units[idx].i.x
                    t = (t - self.units[idx].i.x) / dt
                    return self.units[idx].at(t)

            """
            if self.units[idx].i.contains(t):
                dt = self.units[idx].i.y - self.units[idx].i.x
                t = (t - self.units[idx].i.x) / dt
                return self.units[idx].at(t)
            """

            idx += 1

        return None, None

    def wkt_at(self, t):
        # General solution assuming non-constant sampling.
        idx = 0
        n = len(self.units)

        while idx < n:
            if self.units[idx].i.contains(t):
                if isinstance(self.units[idx], MPU2):
                    return self.units[idx].wkt_at(t)
                else:
                    dt = self.units[idx].i.y - self.units[idx].i.x
                    t = (t - self.units[idx].i.x) / dt
                    return self.units[idx].wkt_at(t)

                """
                dt = self.units[idx].i.y - self.units[idx].i.x
                t = (t - self.units[idx].i.x) / dt
                return self.units[idx].wkt_at(t)
                """

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

#-------------------------------------------------------------------
# Parameters
#-------------------------------------------------------------------

solver_exec_times = 0
solver_exec_time = 0
pass_through_control_points = True
print_intersection_information = True
print_solver_execution_time = True
n_samples = 100
epsilon = 0.0000001			# Spatial eps.
coll = False
interval = Interval(1000, 2000, True, True)
precision = '.2f'
precision0 = '.0f'
operation = 1
eps = 0.000001				# Temporal eps.
err_msg = None
err_code = 0
initial_state = None
p_linear_traj = False
begin_exec_time = 0
precision_0 = '.0f'
TESTING = False
NTESTS = 1
r_s_map = {}
t_eps = 0.05

#-------------------------------------------------------------------
# Get paremeters
#-------------------------------------------------------------------
def get_params():
    global pass_through_control_points
    global print_intersection_information
    global print_solver_execution_time
    global n_samples
    global interval
    global epsilon
    global precision
    global operation
    global err_msg

    global TESTING
    global NTESTS

    if len(sys.argv) == 2:
        TESTING = True
        NTESTS = int(sys.argv[1])
        return

    if sys.argv[4] == "0":
        pass_through_control_points = False
    
    if sys.argv[5] == "0":
        print_intersection_information = False

    if sys.argv[6] == "1":
        print_solver_execution_time = True

    n_samples = int(sys.argv[7])

    v = sys.argv[8].split(',')

    if len(v) != 2:
        err_msg = 'get_params_2() : Invalid interval data!'
        return

    interval.x = float(v[0])
    interval.y = float(v[1])
	
    epsilon = float(sys.argv[9])
    precision = '.' + sys.argv[10] + 'f'
    operation = int(sys.argv[11])

#-------------------------------------------------------------------
# Intersection Functions
#-------------------------------------------------------------------

def get_intersections_3(ms, mp, i, msid, prev_it = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon
    global r_s_map

    s = []
    idxms = 0
    idxmp = 0
    end = 0

    while idxms < len(ms.units) and idxmp < len(mp.units):
        msu = ms.units[idxms]
        mpu = mp.units[idxmp]

        if msu.i.x >= i.y or mpu.i.x >= i.y:
            break

        it0 = msu.i.intersection(i)

        if it0 is None:
            idxms += 1
            continue

        it1 = mpu.i.intersection(i)
        if it1 is None:
            idxmp += 1
            continue

        it = it0.intersection(it1)

        if it != None:
            idx = 0
            n = len(msu.c0.intervals)

            while idx < n:
                it0 = msu.c0.intervals[idx].intersection(it)
                if it0 is None:
                    idx += 1
                    continue

                #col = collinear(msu.c0.curves[idx].cp0, msu.c0.curves[idx].cp1, msu.c0.curves[idx].cp2, msu.c1.curves[idx].cp0, msu.c1.curves[idx].cp1, msu.c1.curves[idx].cp2, mpu.p[0], mpu.p[1])

                dt = msu.c0.intervals[idx].y - msu.c0.intervals[idx].x
                #T = (t - msu.c0.intervals[idx].x) / dt

                msu_dt = dt
                msu_t0 = msu.c0.intervals[idx].x

                c0_cp0_x = msu.c0.curves[idx].cp0.x
                c0_cp1_x = msu.c0.curves[idx].cp1.x
                c0_cp2_x = msu.c0.curves[idx].cp2.x

                c0_cp0_y = msu.c0.curves[idx].cp0.y
                c0_cp1_y = msu.c0.curves[idx].cp1.y
                c0_cp2_y = msu.c0.curves[idx].cp2.y

                c1_cp0_x = msu.c1.curves[idx].cp0.x
                c1_cp1_x = msu.c1.curves[idx].cp1.x
                c1_cp2_x = msu.c1.curves[idx].cp2.x

                c1_cp0_y = msu.c1.curves[idx].cp0.y
                c1_cp1_y = msu.c1.curves[idx].cp1.y
                c1_cp2_y = msu.c1.curves[idx].cp2.y

                #Ax, Ay = msu.c0.curves[idx].at(T)
                #Bx, By = msu.c1.curves[idx].at(T)

                # moving point

                dt = mpu.i.y - mpu.i.x
                #T = (t - mpu.i.x) / dt
                #Cx, Cy = mpu.at(T)

                mpu_t0 = mpu.i.x
                mpu_dt = dt

                x0 = mpu.p[0].x
                y0 = mpu.p[0].y

                dx = mpu.p[1].x - mpu.p[0].x
                dy = mpu.p[1].y - mpu.p[0].y

                #done = False
                col = 0

                # Generic case where not all elements travel in the same trajectory.
                if col == 0:
                    exec_time, r = get_solutions_quartic(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu_dt, msu_t0, x0, y0, dx, dy, mpu_t0, mpu_dt, it0)

                    #f = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By)
                    #exec_time, r = get_solutions(f, t, it0)

                    if len(r) > 0:
                        for root in r:
                            Px, Py = mp.at(root)
                            Ax, Ay, Bx, By = msu.at(root)

                            if on_segment_with_eps2(Ax, Ay, Bx, By, Px, Py, epsilon):
                                if root in r_s_map:
                                    r_s_map[root] = r_s_map[root] + [msid]
                                else:
                                    r_s_map[root] = [msid]

                                s += [root]

                        s.sort()

                    solver_exec_time += exec_time
                    solver_exec_times += 1


                # special cases
                """
                else:
                    Px0, Py0 = mp.at(it0.x)
                    Ax0, Ay0, Bx0, By0 = msu.at(it0.x)

                    Px1, Py1 = mp.at(it0.y)
                    Ax1, Ay1, Bx1, By1 = msu.at(it0.y)

                    sin = (min(Ax0, Bx0) - epsilon <= Px0 and Px0 <= max(Ax0, Bx0) + epsilon) and (min(Ay0, By0) - epsilon <= Py0 and Py0 <= max(Ay0, By0) + epsilon)
                    sou = (min(Ax1, Bx1) - epsilon <= Px1 and Px1 <= max(Ax1, Bx1) + epsilon) and (min(Ay1, By1) - epsilon <= Py1 and Py1 <= max(Ay1, By1) + epsilon)

                    n = len(s)

                    # The MP is inside the MS.
                    if sin and sou:
                        if n == 0:
                            s += [Interval(it0.x, it0.y, True, True)]
                        else:
                            prev = s[n-1]
                            if isinstance(prev, Interval):
                                if it0.x <= prev.y:
                                    prev.y = it0.y
                                else:
                                    s += [Interval(it0.x, it0.y, True, True)]
                            else:
                                if prev == it0.x:
                                    s[n-1] = [Interval(prev, it0.y, True, True)]
                                else:
                                    s += [Interval(it0.x, it0.y, True, True)]
                        done = True
                    elif sin:
                        a0 = None
                        a1 = None
                        a2 = None

                        if col == 1:
                            # Cy - By
                            #f = Cy - By
                            a0 = (-msu_dt**2*mpu_dt*c1_cp0_y + msu_dt**2*mpu_dt*y0 - msu_dt**2*mpu_t0*dy - 2*msu_dt*mpu_dt*c1_cp0_y*msu_t0 + 2*msu_dt*mpu_dt*c1_cp1_y*msu_t0 - mpu_dt*c1_cp0_y*msu_t0**2 + 2*mpu_dt*c1_cp1_y*msu_t0**2 - mpu_dt*c1_cp2_y*msu_t0**2) / (msu_dt**2*mpu_dt)
                            a1 = (+msu_dt**2*dy + 2*msu_dt*mpu_dt*c1_cp0_y - 2*msu_dt*mpu_dt*c1_cp1_y + 2*mpu_dt*c1_cp0_y*msu_t0 - 4*mpu_dt*c1_cp1_y*msu_t0 + 2*mpu_dt*c1_cp2_y*msu_t0) / (msu_dt**2*mpu_dt)
                            a2 = (-mpu_dt*c1_cp0_y + 2*mpu_dt*c1_cp1_y - mpu_dt*c1_cp2_y) / (msu_dt**2*mpu_dt)
                        else:
                            # Cx - Bx
                            #f = Cx - Bx
                            a0 = (-msu_dt**2*mpu_dt*c1_cp0_x + msu_dt**2*mpu_dt*x0 - msu_dt**2*mpu_t0*dx + 2*msu_dt*mpu_dt*c1_cp1_x*msu_t0 - 2*msu_dt*mpu_dt*c1_cp0_x*msu_t0 - c1_cp2_x*mpu_dt*msu_t0**2 + 2*mpu_dt*c1_cp1_x*msu_t0**2 - mpu_dt*c1_cp0_x*msu_t0**2) / (msu_dt**2*mpu_dt)
                            a1 = (+msu_dt**2*dx - 2*msu_dt*mpu_dt*c1_cp1_x + 2*msu_dt*mpu_dt*c1_cp0_x + 2*c1_cp2_x*mpu_dt*msu_t0 - 4*mpu_dt*c1_cp1_x*msu_t0 + 2*mpu_dt*c1_cp0_x*msu_t0) / (msu_dt**2*mpu_dt)
                            a2 = (-c1_cp2_x*mpu_dt + 2*mpu_dt*c1_cp1_x - mpu_dt*c1_cp0_x) / (msu_dt**2*mpu_dt)

                        #exec_time, r = get_solutions(f, t, it0)
                        exec_time, r = get_solutions_quad(a0, a1, a2)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        if len(r) != 1:
                            print('ERR: Unexpected intersection instant.')
                            sys.exit()

                        Px1, Py1 = mp.at(r[0])
                        Ax1, Ay1, Bx1, By1 = msu.at(r[0])

                        if not (min(Ax1, Bx1) - epsilon <= Px1 and Px1 <= max(Ax1, Bx1) + epsilon) and (min(Ay1, By1) - epsilon <= Py1 and Py1 <= max(Ay1, By1) + epsilon):
                            print('ERR: Intersection instant is not on the MS, as expected.')
                            sys.exit()

                        if n == 0:
                            s += [Interval(it0.x, r[0], True, True)]
                        else:
                            prev = s[n-1]
                            if isinstance(prev, Interval):
                                if it0.x <= prev.y:
                                    prev.y = r[0]
                                else:
                                    s += [Interval(it0.x, r[0], True, True)]
                            else:
                                if prev == it0.x:
                                    s[n-1] = [Interval(prev, r[0], True, True)]
                                else:
                                    s += [Interval(it0.x, r[0], True, True)]
                        done = True
                    else:
                        a0 = None
                        a1 = None
                        a2 = None

                        if col == 1:
                            #f = Cy - Ay
                            a0 = (-msu_dt**2*c0_cp0_y*mpu_dt + msu_dt**2*mpu_dt*y0 - msu_dt**2*mpu_t0*dy - 2*msu_dt*c0_cp0_y*mpu_dt*msu_t0 + 2*msu_dt*c0_cp1_y*mpu_dt*msu_t0 - c0_cp0_y*mpu_dt*msu_t0**2 + 2*c0_cp1_y*mpu_dt*msu_t0**2 - mpu_dt*c0_cp2_y*msu_t0**2) / (msu_dt**2*mpu_dt)
                            a1 = (+msu_dt**2*dy + 2*msu_dt*c0_cp0_y*mpu_dt - 2*msu_dt*c0_cp1_y*mpu_dt + 2*c0_cp0_y*mpu_dt*msu_t0 - 4*c0_cp1_y*mpu_dt*msu_t0 + 2*mpu_dt*c0_cp2_y*msu_t0) / (msu_dt**2*mpu_dt)
                            a2 = (-c0_cp0_y*mpu_dt + 2*c0_cp1_y*mpu_dt - mpu_dt*c0_cp2_y) / (msu_dt**2*mpu_dt)							
                        else:
                            #f = Cx - Ax
                            a0 = (-c0_cp0_x*msu_dt**2*mpu_dt - 2*c0_cp0_x*msu_dt*mpu_dt*msu_t0 - c0_cp0_x*mpu_dt*msu_t0**2 + 2*c0_cp1_x*msu_dt*mpu_dt*msu_t0 + 2*c0_cp1_x*mpu_dt*msu_t0**2 - c0_cp2_x*mpu_dt*msu_t0**2 + msu_dt**2*mpu_dt*x0 - msu_dt**2*mpu_t0*dx) / (msu_dt**2*mpu_dt)
                            a1 = (+2*c0_cp0_x*msu_dt*mpu_dt + 2*c0_cp0_x*mpu_dt*msu_t0 - 2*c0_cp1_x*msu_dt*mpu_dt - 4*c0_cp1_x*mpu_dt*msu_t0 + 2*c0_cp2_x*mpu_dt*msu_t0 + msu_dt**2*dx) / (msu_dt**2*mpu_dt)
                            a2 = (-c0_cp0_x*mpu_dt + 2*c0_cp1_x*mpu_dt - c0_cp2_x*mpu_dt) / (msu_dt**2*mpu_dt)

                        #exec_time, r0 = get_solutions(f, t, it0)
                        exec_time, r = get_solutions_quad(a0, a1, a2)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        if col == 1:
                            #f = Cy - By
                            a0 = (-msu_dt**2*mpu_dt*c1_cp0_y + msu_dt**2*mpu_dt*y0 - msu_dt**2*mpu_t0*dy - 2*msu_dt*mpu_dt*c1_cp0_y*msu_t0 + 2*msu_dt*mpu_dt*c1_cp1_y*msu_t0 - mpu_dt*c1_cp0_y*msu_t0**2 + 2*mpu_dt*c1_cp1_y*msu_t0**2 - mpu_dt*c1_cp2_y*msu_t0**2) / (msu_dt**2*mpu_dt)
                            a1 = (+msu_dt**2*dy + 2*msu_dt*mpu_dt*c1_cp0_y - 2*msu_dt*mpu_dt*c1_cp1_y + 2*mpu_dt*c1_cp0_y*msu_t0 - 4*mpu_dt*c1_cp1_y*msu_t0 + 2*mpu_dt*c1_cp2_y*msu_t0) / (msu_dt**2*mpu_dt)
                            a2 = (-mpu_dt*c1_cp0_y + 2*mpu_dt*c1_cp1_y - mpu_dt*c1_cp2_y) / (msu_dt**2*mpu_dt)
                        else:
                            #f = Cx - Bx
                            a0 = (-msu_dt**2*mpu_dt*c1_cp0_x + msu_dt**2*mpu_dt*x0 - msu_dt**2*mpu_t0*dx + 2*msu_dt*mpu_dt*c1_cp1_x*msu_t0 - 2*msu_dt*mpu_dt*c1_cp0_x*msu_t0 - c1_cp2_x*mpu_dt*msu_t0**2 + 2*mpu_dt*c1_cp1_x*msu_t0**2 - mpu_dt*c1_cp0_x*msu_t0**2) / (msu_dt**2*mpu_dt)
                            a1 = (+msu_dt**2*dx - 2*msu_dt*mpu_dt*c1_cp1_x + 2*msu_dt*mpu_dt*c1_cp0_x + 2*c1_cp2_x*mpu_dt*msu_t0 - 4*mpu_dt*c1_cp1_x*msu_t0 + 2*mpu_dt*c1_cp0_x*msu_t0) / (msu_dt**2*mpu_dt)
                            a2 = (-c1_cp2_x*mpu_dt + 2*mpu_dt*c1_cp1_x - mpu_dt*c1_cp0_x) / (msu_dt**2*mpu_dt)

                        #exec_time, r1 = get_solutions(f, t, it0)
                        exec_time, r = get_solutions_quad(a0, a1, a2)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        r = r0 + r1
                """

                # check if roots are on the segment (are valid)
                # roots not in the interval have already been discarded in get_solutions_quartic

                """
                #if not done:
                #roots = []

                for root in r:
                    Px, Py = mp.at(root)
                    Ax, Ay, Bx, By = msu.at(root)

                    if on_segment_with_eps(Ax, Ay, Bx, By, Px, Py, epsilon):
                        s += [root]

                #s = roots
                s.sort()
                """

                idx += 1

        # next unit(s)

        if msu.i.y == mpu.i.y:
            idxms += 1
            idxmp += 1
        elif msu.i.y < mpu.i.y:
            idxms += 1
        else:
            idxmp += 1

    # sort current and previous intersections

    if prev_it != None:
        i = 0
        j = 0

        _sorted = []

        n = len(prev_it)
        m = len(s)

        while i < n and j < m:
            x1 = prev_it[i]
            x2 = s[j]

            if x1 < x2:
                _sorted += [x1]
                i += 1
            elif x1 > x2:
                _sorted += [x2]
                j += 1
            else:
                _sorted += [x1]
                i += 1
                j += 1

        while i < n:
            _sorted += [prev_it[i]]
            i += 1

        while j < m:
            _sorted += [s[j]]
            j += 1

        s = _sorted

    return s

def get_intersections_4(ms, mp, i, msid, prev_it = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon
    global r_s_map

    s = []
    idxms = 0
    idxmp = 0
    end = 0

    while idxms < len(ms.units) and idxmp < len(mp.units):
        msu = ms.units[idxms]
        mpu = mp.units[idxmp]

        if msu.i.x >= i.y or mpu.i.x >= i.y:
            break

        it0 = msu.i.intersection(i)

        if it0 is None:
            idxms += 1
            continue

        it1 = mpu.i.intersection(i)
        if it1 is None:
            idxmp += 1
            continue

        it = it0.intersection(it1)

        if it != None:
            idx = 0
            n = len(msu.c0.intervals)

            while idx < n:
                it0 = msu.c0.intervals[idx].intersection(it)
                if it0 is None:
                    idx += 1
                    continue

                # moving region

                dt = msu.c0.intervals[idx].y - msu.c0.intervals[idx].x

                msu_dt = dt
                msu_t0 = msu.c0.intervals[idx].x

                c0_cp0_x = msu.c0.curves[idx].cp0.x
                c0_cp1_x = msu.c0.curves[idx].cp1.x
                c0_cp2_x = msu.c0.curves[idx].cp2.x

                c0_cp0_y = msu.c0.curves[idx].cp0.y
                c0_cp1_y = msu.c0.curves[idx].cp1.y
                c0_cp2_y = msu.c0.curves[idx].cp2.y

                c1_cp0_x = msu.c1.curves[idx].cp0.x
                c1_cp1_x = msu.c1.curves[idx].cp1.x
                c1_cp2_x = msu.c1.curves[idx].cp2.x

                c1_cp0_y = msu.c1.curves[idx].cp0.y
                c1_cp1_y = msu.c1.curves[idx].cp1.y
                c1_cp2_y = msu.c1.curves[idx].cp2.y

                # moving point

                dt = mpu.c.intervals[0].y - mpu.c.intervals[0].x
                mpu_dt = dt
                mpu_t0 = mpu.c.intervals[0].x

                c2_cp0_x = mpu.c.curves[0].cp0.x
                c2_cp1_x = mpu.c.curves[0].cp1.x
                c2_cp2_x = mpu.c.curves[0].cp2.x

                c2_cp0_y = mpu.c.curves[0].cp0.y
                c2_cp1_y = mpu.c.curves[0].cp1.y
                c2_cp2_y = mpu.c.curves[0].cp2.y

                #done = False
                case = 0

                #aabb filter step

                flag = not (msu.left > mpu.right or msu.right < mpu.left or msu.top < mpu.bottom or msu.bottom > mpu.top)
                if not flag:
                    case = 1
                    #done = True

                # Generic case
                if case == 0:
                    exec_time, r = get_solutions_quartic2(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu_dt, msu_t0, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, mpu_t0, mpu_dt, it0)

                    solver_exec_time += exec_time
                    solver_exec_times += 1

                    if len(r) > 0:
                        #roots = []

                        for root in r:
                            Px, Py = mp.at(root)
                            Ax, Ay, Bx, By = msu.at(root)

                            if on_segment_with_eps2(Ax, Ay, Bx, By, Px, Py, epsilon):
                                if root in r_s_map:
                                    r_s_map[root] = r_s_map[root] + [msid]
                                else:
                                    r_s_map[root] = [msid]

                                s += [root]

                        #s = roots
                        #s.sort()
                # special cases
                #else:
                #    pass

                idx += 1

        if msu.i.y == mpu.i.y:
            idxms += 1
            idxmp += 1
        elif msu.i.y < mpu.i.y:
            idxms += 1
        else:
            idxmp += 1

    # sort current and previous intersections
    s.sort()

    if prev_it != None:
        i = 0
        j = 0

        _sorted = []

        n = len(prev_it)
        m = len(s)

        while i < n and j < m:
            x1 = prev_it[i]
            x2 = s[j]

            if x1 < x2:
                _sorted += [x1]
                i += 1
            elif x1 > x2:
                _sorted += [x2]
                j += 1
            else:
                _sorted += [x1]
                i += 1
                j += 1

        while i < n:
            _sorted += [prev_it[i]]
            i += 1

        while j < m:
            _sorted += [s[j]]
            j += 1

        s = _sorted

    return s

def process_intersections2(intersections, mp, msegs, initial_state, final_state, ccw):
    global r_s_map
    global t_eps

    n = len(intersections)

    #print(r_s_map)
    #print(intersections)

    """	
    if n == 1:
        intersection = intersections[0]

        # Disjoint
        if initial_state == None:
            # Touch
            if final_state == None:
                pass
            elif final_state == State.Inside:
                if intersection < interval.y:
                    I = Interval(intersection, interval.y, True, True)
                    intersections = [I]
            # Touch
            elif final_state == State.Touch:
                if intersection != interval.y:
                    print_error(-1, 'Only one intersection, but not the one expected (1 Case).')
        # Inside
        elif initial_state == State.Inside:
            if intersection > interval.x:
                I = Interval(interval.x, intersection, True, True)
                intersections = [I]
        # Touch
        elif initial_state == State.Touch:
            if intersection != interval.x:
                print_error(-1, 'process_intersections() Only one intersection, but not the one expected (2 Case).')
    """
    if n > 1:
        i = 0
        _intersections = []

        if initial_state == None or initial_state == State.Touch:
            while i < n - 1:
                t0 = intersections[i]
                t1 = intersections[i+1]

                # check if it has 1+ msegs in r_s_map[t0].
                # can use that some how to make more efficient computations.
                ms_idx = r_s_map[t0][0]
                ms = msegs[ms_idx]
                dt = (t1 - t0)
                t = t0 + t_eps
                if t_eps > dt:
                    t = (t0 + t1) / 2

                x0, y0, x1, y1 = ms.at(t)
                Px, Py = mp.at(t)

                if Px == x0:
                    nn = len(msegs)
                    if ccw:
                        ms1_idx = ms_idx - 1
                        if ms_idx == 0:
                            ms1_idx = nn - 1

                    else:
                        ms1_idx = ms_idx + 1
                        if ms_idx == nn - 1:
                            ms1_idx = 0

                    ms = msegs[ms1_idx]
                    x0, y0, x1, y1 = ms.at(t)
                    #print('1')
                elif Px == x1:
                    nn = len(msegs)
                    if ccw:
                        ms1_idx = ms_idx + 1
                        if ms_idx == nn - 1:
                            ms1_idx = 0
                    else:
                        ms1_idx = ms_idx - 1
                        if ms_idx == 0:
                            ms1_idx = nn - 1

                    ms = msegs[ms1_idx]
                    x0, y0, x1, y1 = ms.at(t)
                    #print('2')

                #else:
                #ccw
                dir = 1
                if not ccw:
                    dir = -1

                if direction2(x0, y0, x1, y1, Px, Py) == dir:
                    I = Interval(t0, t1, True, True)
                    _intersections += [I]
                    i += 2
                else:
                    if i == n-2:
                        _intersections += [t0, t1]
                        i += 2
                    else:
                        _intersections += [t0]
                        i += 1
                #print('G')

                """
                t = (t0 + t1) / 2

                Px, Py = mp.at(t)

                coords = []
                k = 0
                for mseg in msegs:
                    x0, y0, x1, y1 = mseg.at(t)

                    if k == 0:
                        coords += [[x0, y0]]
                        k = 1

                    coords += [[x1, y1]]               
            
                reg = Polygon(coords)

                if not reg.is_valid:
                    print_error(-1, 'process_intersections() : Invalid Observation.')
                        
                if not reg.is_simple:
                    print_error(-1, 'process_intersections() : Non-simple Observation.')

                if shapely.geometry.Point(Px, Py).disjoint(reg):
                    if i == n-2:
                        _intersections += [t0, t1]
                        i += 2
                    else:
                        _intersections += [t0]
                        i += 1
                else:
                    I = Interval(t0, t1, True, True)
                    _intersections += [I]
                    i += 2
                """

                """
                if shapely.geometry.Point(Px, Py).within(reg):
                    I = Interval(t0, t1, True, True)
                    _intersections += [I]
                    i += 2
                else:
                    if i == n-2:
                        _intersections += [t0, t1]
                        i += 2
                    else:
                        _intersections += [t0]
                        i += 1
                """
        elif initial_state == State.Inside:
            t0 = intersections[0]
            t1 = intersections[1]

            I = Interval(t0, t1, True, True)
            _intersections += [I]
            i += 2

            while i < n - 1:
                t0 = intersections[i]
                t1 = intersections[i+1]

                ms = msegs[r_s_map[t0][0]]
                dt = (t1 - t0)
                t = t0 + t_eps
                if t_eps > dt:
                    t = (t0 + t1) / 2

                x0, y0, x1, y1 = ms.at(t)
                Px, Py = mp.at(t)

                if Px == x0:
                    print('1')
                elif Px == x1:
                    print('2')
                else:
                    #ccw
                    dir = 1
                    if not ccw:
                        dir = -1

                    if direction2(x0, y0, x1, y1, Px, Py) == dir:
                        I = Interval(t0, t1, True, True)
                        _intersections += [I]
                        i += 2
                    else:
                        if i == n-2:
                            _intersections += [t0, t1]
                            i += 2
                        else:
                            _intersections += [t0]
                            i += 1

                """
                t0 = intersections[i]
                t1 = intersections[i+1]

                t = (t0 + t1) / 2

                Px, Py = mp.at(t)

                coords = []
                k = 0
                for mseg in msegs:
                    x0, y0, x1, y1 = mseg.at(t)

                    if k == 0:
                        coords += [[x0, y0]]
                        k = 1

                    coords += [[x1, y1]]               
            
                reg = Polygon(coords)

                if not reg.is_valid:
                    print_error(-1, 'process_intersections() : Invalid Observation (2 condition).')
                        
                if not reg.is_simple:
                    print_error(-1, 'process_intersections() : Non-simple Observation (2 condition).')

                if shapely.geometry.Point(Px, Py).within(reg):
                    I = Interval(t0, t1, True, True)
                    _intersections += [I]
                    i += 2
                else:
                    if i == n-2:
                        _intersections += [t0, t1]
                        i += 2
                    else:
                        _intersections += [t0]
                        i += 1
                """
        """
        elif initial_state == State.Touch:
            while i < n - 1:
                t0 = intersections[i]
                t1 = intersections[i+1]

                t = (t0 + t1) / 2

                Px, Py = mp.at(t)

                coords = []
                k = 0
                for mseg in msegs:
                    x0, y0, x1, y1 = mseg.at(t)

                    if k == 0:
                        coords += [[x0, y0]]
                        k = 1

                    coords += [[x1, y1]]               
            
                reg = Polygon(coords)

                if not reg.is_valid:
                    print_error(-1, 'process_intersections() : Invalid Observation.')
                        
                if not reg.is_simple:
                    print_error(-1, 'process_intersections() : Non-simple Observation.')

                if shapely.geometry.Point(Px, Py).within(reg):
                    I = Interval(t0, t1, True, True)
                    _intersections += [I]
                    i += 2
                else:
                    if i == n-2:
                        _intersections += [t0, t1]
                        i += 2
                    else:
                        _intersections += [t0]
                        i += 1
        """
        intersections = _intersections

    return intersections

def process_intersections(intersections, mp, msegs, initial_state, final_state, ccw):
    global r_s_map
    global t_eps

    n = len(intersections)

    if n > 1:
        i = 0
        _intersections = []

        if initial_state == None or initial_state == State.Touch:
            while i < n - 1:
                t0 = intersections[i]
                t1 = intersections[i+1]

                # check if it has 1+ msegs in r_s_map[t0].
                # can use that some how to make more efficient computations.

                ms_idx = r_s_map[t0][0]
                ms = msegs[ms_idx]

                dt = (t1 - t0)
                t = t0 + t_eps
                if t_eps > dt:
                    t = (t0 + t1) / 2

                x0, y0, x1, y1 = ms.at(t)
                Px, Py = mp.at(t)

                dir = 1
                if not ccw:
                    dir = -1

                r = direction2(x0, y0, x1, y1, Px, Py)

                if len(r_s_map[t0]) > 1:
                    ms_idx = r_s_map[t0][1]
                    ms = msegs[ms_idx]
                    x0, y0, x1, y1 = ms.at(t)
                    rr = direction2(x0, y0, x1, y1, Px, Py)

                    if r != rr:
                        r = -dir

                if r == dir:
                    _intersections += [Interval(t0, t1, True, True)]
                    i += 2
                else:
                    if i == n-2:
                        _intersections += [t0, t1]
                        i += 2
                    else:
                        _intersections += [t0]
                        i += 1

                """
                if Px == x0:
                    nn = len(msegs)
                    if ccw:
                        ms1_idx = ms_idx - 1
                        if ms_idx == 0:
                            ms1_idx = nn - 1

                    else:
                        ms1_idx = ms_idx + 1
                        if ms_idx == nn - 1:
                            ms1_idx = 0

                    ms = msegs[ms1_idx]
                    x0, y0, x1, y1 = ms.at(t)
                    #print('1')
                elif Px == x1:
                    nn = len(msegs)
                    if ccw:
                        ms1_idx = ms_idx + 1
                        if ms_idx == nn - 1:
                            ms1_idx = 0
                    else:
                        ms1_idx = ms_idx - 1
                        if ms_idx == 0:
                            ms1_idx = nn - 1

                    ms = msegs[ms1_idx]
                    x0, y0, x1, y1 = ms.at(t)
                    #print('2')

                #else:
                #ccw
                dir = 1
                if not ccw:
                    dir = -1

                if direction2(x0, y0, x1, y1, Px, Py) == dir:
                    I = Interval(t0, t1, True, True)
                    _intersections += [I]
                    i += 2
                else:
                    if i == n-2:
                        _intersections += [t0, t1]
                        i += 2
                    else:
                        _intersections += [t0]
                        i += 1
                """
        elif initial_state == State.Inside:
            t0 = intersections[0]
            t1 = intersections[1]

            _intersections += [Interval(t0, t1, True, True)]
            i += 2

            while i < n - 1:
                t0 = intersections[i]
                t1 = intersections[i+1]

                ms_idx = r_s_map[t0][0]
                ms = msegs[ms_idx]

                dt = (t1 - t0)
                t = t0 + t_eps
                if t_eps > dt:
                    t = (t0 + t1) / 2

                x0, y0, x1, y1 = ms.at(t)
                Px, Py = mp.at(t)

                dir = 1
                if not ccw:
                    dir = -1

                r = direction2(x0, y0, x1, y1, Px, Py)

                if len(r_s_map[t0]) > 1:
                    ms_idx = r_s_map[t0][1]
                    ms = msegs[ms_idx]
                    x0, y0, x1, y1 = ms.at(t)
                    rr = direction2(x0, y0, x1, y1, Px, Py)

                    if r != rr:
                        r = -dir

                if r == dir:
                    _intersections += [Interval(t0, t1, True, True)]
                    i += 2
                else:
                    if i == n-2:
                        _intersections += [t0, t1]
                        i += 2
                    else:
                        _intersections += [t0]
                        i += 1

                """
                ms = msegs[r_s_map[t0][0]]
                dt = (t1 - t0)
                t = t0 + t_eps
                if t_eps > dt:
                    t = (t0 + t1) / 2

                x0, y0, x1, y1 = ms.at(t)
                Px, Py = mp.at(t)

                if Px == x0:
                    print('1')
                elif Px == x1:
                    print('2')
                else:
                    #ccw
                    dir = 1
                    if not ccw:
                        dir = -1

                    if direction2(x0, y0, x1, y1, Px, Py) == dir:
                        I = Interval(t0, t1, True, True)
                        _intersections += [I]
                        i += 2
                    else:
                        if i == n-2:
                            _intersections += [t0, t1]
                            i += 2
                        else:
                            _intersections += [t0]
                            i += 1
                """
        
        intersections = _intersections

    return intersections

#-------------------------------------------------------------------
# MS Functions
#-------------------------------------------------------------------

def get_moving_segs_from_observations2(p, q, t0, t1):
    global err_msg
    global err_code
	
    """
    print('')
    print(p.wkt)
    print('')
    #print(q.wkt)
    p = shapely.geometry.polygon.orient(p, sign=1.0)
    q = shapely.geometry.polygon.orient(q, sign=1.0)
    print(p.wkt)
    #print(q.wkt)
    print('')
    """

    # get moving segments from p to q

    msegs = get_msegs_simple_polygons_with_corr(p, q)

    # get moving segments at t = 0.5
	
    coords = []
    t = 0.5

    nmsegs = len(msegs)
    k = 1

    xi, yi, xf, yf = msegs[0].at(t)

    coords += [[xi, yi], [xf, yf]]

    while k < nmsegs:
        xi, yi, xf, yf = msegs[k].at(t)
        coords += [[xf, yf]]
        k += 1

    """
    k = 0
    for mseg in msegs:
        xi, yi, xf, yf = mseg.at(t)

        if k == 0:
            coords += [[xi, yi]]
            k = 1

        coords += [[xf, yf]]
    """

    g = Polygon(coords)

    if not g.is_valid:
        print_error(11, 'Invalid Observation.')
                        
    if not g.is_simple:
        print_error(12, 'Non-simple Observation.')

    g1_coords = p.exterior.coords
    g2_coords = g.exterior.coords
    g3_coords = q.exterior.coords

    MS = []
    N = len(g1_coords) - 1
    i = 1

    prev = str(g1_coords[0][0]) + ',' + str(g1_coords[0][1]) + ',' + str(g2_coords[0][0]) + ',' + str(g2_coords[0][1]) + ',' + str(g3_coords[0][0]) + ',' + str(g3_coords[0][1]) + '#'

    interval = str(t0) + ',' + str(t1)
    interval = interval + ':' + interval
	
    while i < N:
        curr = str(g1_coords[i][0]) + ',' + str(g1_coords[i][1]) + ',' + str(g2_coords[i][0]) + ',' + str(g2_coords[i][1]) + ',' + str(g3_coords[i][0]) + ',' + str(g3_coords[i][1]) + '#'

        MS += [prev + curr + interval]
        prev = curr
        i += 1

    curr = str(g1_coords[0][0]) + ',' + str(g1_coords[0][1]) + ',' + str(g2_coords[0][0]) + ',' + str(g2_coords[0][1]) + ',' + str(g3_coords[0][0]) + ',' + str(g3_coords[0][1]) + '#'
    MS += [prev + curr + interval]

    return MS

def get_moving_segs_from_observations(p, q, t0, t1):
    #global err_msg
    #global err_code

    # get moving segments from p to q

    msegs = get_msegs_simple_polygons_with_corr(p, q)

    # get ob at t = 0.5

    coords = []
    t = 0.5

    nmsegs = len(msegs)
    k = 1

    xi, yi, xf, yf = msegs[0].at(t)

    coords += [[xi, yi], [xf, yf]]

    while k < nmsegs:
        xi, yi, xf, yf = msegs[k].at(t)
        coords += [[xf, yf]]
        k += 1

    g = Polygon(coords)

    if not g.is_valid:
        print_error(11, 'Invalid Observation.')
                        
    if not g.is_simple:
        print_error(12, 'Non-simple Observation.')

    # get observations

    g1_coords = p.exterior.coords
    g2_coords = g.exterior.coords
    g3_coords = q.exterior.coords

    MS = []
    N = len(g1_coords) - 1
    i = 1

    #prev = str(g1_coords[0][0]) + ',' + str(g1_coords[0][1]) + ',' + str(g2_coords[0][0]) + ',' + str(g2_coords[0][1]) + ',' + str(g3_coords[0][0]) + ',' + str(g3_coords[0][1]) + '#'
    prev = (g1_coords[0][0], g1_coords[0][1], g2_coords[0][0], g2_coords[0][1], g3_coords[0][0], g3_coords[0][1])

    #interval = str(t0) + ',' + str(t1)
    #interval = interval + ':' + interval
	
    interval = (t0, t1, t0, t1)

    while i < N:
        #curr = str(g1_coords[i][0]) + ',' + str(g1_coords[i][1]) + ',' + str(g2_coords[i][0]) + ',' + str(g2_coords[i][1]) + ',' + str(g3_coords[i][0]) + ',' + str(g3_coords[i][1]) + '#'
        curr = (g1_coords[i][0], g1_coords[i][1], g2_coords[i][0], g2_coords[i][1], g3_coords[i][0], g3_coords[i][1])

        MS += [[prev, curr, interval]]
        prev = curr
        i += 1

    #curr = str(g1_coords[0][0]) + ',' + str(g1_coords[0][1]) + ',' + str(g2_coords[0][0]) + ',' + str(g2_coords[0][1]) + ',' + str(g3_coords[0][0]) + ',' + str(g3_coords[0][1]) + '#'
    curr = (g1_coords[0][0], g1_coords[0][1], g2_coords[0][0], g2_coords[0][1], g3_coords[0][0], g3_coords[0][1])
    MS += [[prev, curr, interval]]

    return MS

def create_moving_segment(units, pass_through_control_points):
    ms = MovingSegment()

    for u in units:
        c0 = CCurve()
        c1 = CCurve()

        #u = u.split("#")
        t = 0.5

        #if len(u) != 3:
        #    print_error(-1, 'Invalid unit data! ' + u)

        cp0 = u[0]
        cp1 = u[1]
        intervals = u[2]

        #print(u)
        #print(intervals)

        """
        M = len(cp0)
        N = len(cp0)

        if M != N:
            print_error(-1, 'Different number of control points! ' + cp0 + ' : ' + cp1)

        if (len(cp0) - 6) % 2 != 0 or (len(cp1) - 6) % 2 != 0:
            print_error(-1, 'Invalid control points data! ' + cp0 + ' : ' + cp1)

        m = ((len(cp0) - 6) / 4) + 1

        if (len(intervals)) - 1 != m:
            print_error(-1, 'Invalid interval data! ' + str(len(intervals) - 1) + ' : ' + str(m))
        """

        #step = 4
        #n = len(cp0)
        #idx = 0

        #k = 0

        #while idx < n - 5:
        #i = intervals[k].split(",")
        #i = Interval(float(i[0]), float(i[1]), True, False)
        i = Interval(intervals[0], intervals[1], True, False)

        p0 = Point(cp0[0], cp0[1])
        p1 = Point(cp0[2], cp0[3])
        p2 = Point(cp0[4], cp0[5])

        if pass_through_control_points:
            x = 2 * p1.x - t * p0.x - t * p2.x
            y = 2 * p1.y - t * p0.y - t * p2.y
            c = QuadBezierCurve(p0, Point(x, y), p2)
        else:
            c = QuadBezierCurve(p0, p1, p2)

        c0.add_curve(c, i)

        p0 = Point(cp1[0], cp1[1])
        p1 = Point(cp1[2], cp1[3])
        p2 = Point(cp1[4], cp1[5])

        if pass_through_control_points:
            x = 2 * p1.x - t * p0.x - t * p2.x
            y = 2 * p1.y - t * p0.y - t * p2.y
            c = QuadBezierCurve(p0, Point(x, y), p2)
        else:
            c = QuadBezierCurve(p0, p1, p2)

        c1.add_curve(c, i)

        #idx += step
        #k += 1

        #i = intervals[k].split(",")
        #i = Interval(float(i[0]), float(i[1]), True, False)
        i = Interval(intervals[2], intervals[3], True, False)
        u = MSU(c0, c1, i)

        ms.add_unit(u)

    return ms

def get_msegs_simple_polygons_with_corr(p, q):
    msegs = []

    pcoords =  p.exterior.coords
    qcoords =  q.exterior.coords

    n = len(pcoords)
    i = 0
        
    while i < n - 1:
        A = Point(pcoords[i][0], pcoords[i][1])
        B = Point(pcoords[i+1][0], pcoords[i+1][1])

        C = Point(qcoords[i][0], qcoords[i][1])
        D = Point(qcoords[i+1][0], qcoords[i+1][1])
                        
        msegs += [MSeg(A, B, C, D, 0, 1, False)]
        i += 1
    
    return msegs

def create_moving_segment2(units, pass_through_control_points):
    ms = MovingSegment()

    for u in units:
        c0 = CCurve()
        c1 = CCurve()

        u = u.split("#")
        t = 0.5

        if len(u) != 3:
            print_error(-1, 'Invalid unit data! ' + u)

        cp0 = u[0].split(",")
        cp1 = u[1].split(",")
        intervals = u[2].split(":")

        if len(cp0) != len(cp1):
            print_error(-1, 'Different number of control points! ' + cp0 + ' : ' + cp1)

        if (len(cp0) - 6) % 2 != 0 or (len(cp1) - 6) % 2 != 0:
            print_error(-1, 'Invalid control points data! ' + cp0 + ' : ' + cp1)

        m = ((len(cp0) - 6) / 4) + 1

        if (len(intervals)) - 1 != m:
            print_error(-1, 'Invalid interval data! ' + str(len(intervals) - 1) + ' : ' + str(m))

        step = 4
        n = len(cp0)
        idx = 0

        k = 0

        while idx < n - 5:
            i = intervals[k].split(",")
            i = Interval(float(i[0]), float(i[1]), True, False)

            p0 = Point(float(cp0[idx]), float(cp0[idx+1]))
            p1 = Point(float(cp0[idx+2]), float(cp0[idx+3]))
            p2 = Point(float(cp0[idx+4]), float(cp0[idx+5]))

            if pass_through_control_points:
                x = 2 * p1.x - t * p0.x - t * p2.x
                y = 2 * p1.y - t * p0.y - t * p2.y
                c = QuadBezierCurve(p0, Point(x, y), p2)
            else:
                c = QuadBezierCurve(p0, p1, p2)

            c0.add_curve(c, i)

            p0 = Point(float(cp1[idx]), float(cp1[idx+1]))
            p1 = Point(float(cp1[idx+2]), float(cp1[idx+3]))
            p2 = Point(float(cp1[idx+4]), float(cp1[idx+5]))

            if pass_through_control_points:
                x = 2 * p1.x - t * p0.x - t * p2.x
                y = 2 * p1.y - t * p0.y - t * p2.y

                c = QuadBezierCurve(p0, Point(x, y), p2)
            else:
                c = QuadBezierCurve(p0, p1, p2)

            c1.add_curve(c, i)

            idx += step
            k += 1

        i = intervals[k].split(",")
        i = Interval(float(i[0]), float(i[1]), True, False)
        u = MSU(c0, c1, i)

        ms.add_unit(u)

    return ms

#-------------------------------------------------------------------
# CG functions
#-------------------------------------------------------------------

def direction(p, q, r):
    #signed_area of triangle pqr
    signed_area = ((q.x - p.x) * (r.y - p.y)) - ((q.y - p.y) * (r.x - p.x))

    #A(pqr) > 0 if and only if p, q, r are in ccw order
    if signed_area > 0:
        return 1
    #cw
    elif signed_area < 0:
        return -1

    #collinear
    return 0

def direction2(px, py, qx, qy, rx, ry):
    #signed_area of triangle pqr
    signed_area = ((qx - px) * (ry - py)) - ((qy - py) * (rx - px))

    #A(pqr) > 0 if and only if p, q, r are in ccw order
    if signed_area > 0:
        return 1
    #cw
    elif signed_area < 0:
        return -1

    #collinear
    return 0

def get_states(p, q, mpoint):
    inicial_state = None
    final_state = None

    i = mpoint.units[0].i

    x0, y0 = mpoint.units[0].at(i.x)
    point = shapely.geometry.Point(x0, y0)

    if point.touches(p):
        inicial_state = State.Touch
    elif point.within(p):
        inicial_state = State.Inside

    x0, y0 = mpoint.units[0].at(i.y)
    point = shapely.geometry.Point(x0, y0)

    if point.touches(q):
        final_state = State.Touch
    elif point.within(q):
        final_state = State.Inside

    return inicial_state, final_state

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

#-------------------------------------------------------------------
# Output functions
#-------------------------------------------------------------------

def print_error(err_code, err_message):
    print('Polygon Empty')
    print('LineString Empty')
    print(err_code)
    print(err_message)

    if print_intersection_information:
        print('NI: 0:')

    if print_solver_execution_time:
        print('Exec. Time: 0sec, NE: 0')

    sys.exit()

def get_intersection_information(intersection_instants, msegs, mp, op):
    add_comma = False

    if op == Operation.Intersects.value:
        info = "Intersects: "
    elif op == Operation.Disjoint.value:
        info = "Disjoint: "
    elif op == Operation.Touches.value:
        info = "Touches: "
    elif op == Operation.Within.value:
        info = "Within: "
    elif op == Operation.Contains.value:
        info = "Contains: "

    for t in intersection_instants:
        if add_comma:
            info += ", "
        else:
            add_comma = True

        if isinstance(t, Interval):
            P0x, P0y = mp.at(t.x)
            P1x, P1y = mp.at(t.y)

            if t.l:
                info += '['
            else:
                info += ']'

            info += format(t.x, precision) + ", " + format(t.y, precision)

            if t.r:
                info += ']'
            else:
                info += '['

        else:
            Px, Py = mp.at(t)
			
            info += 't: ' + format(t, precision) #+ " >> (x: " + format(Px, precision) + ', y: ' + format(Py, precision) + ')'

    return info

def get_samples_for_out(MS, mp, i, n_samples, s):
    n = (n_samples - 1)
    k = 0
    dt = i.y - i.x
    eq = False

    J = 0
    T = []
    K = []
    for I in s:
        if isinstance(I, Interval):
            T += [I.x, I.y]

            B = 1
            F = 1

            if not I.l:
                B = 0

            if not I.r:
                F = 0

            K += [B, F]
        else:
            T += [I]
            K += [1]

    N = len(T)

    for j in range(0, n_samples):
        t = i.x + dt * (float(j) / n)

        out = 0
        flag = False

        if J < N and t >= T[J]:
            t = T[J]
            out = K[J]
            J += 1
            flag = True

        mline = get_mline(MS, t)

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    print(mline.wkt)
                    print(mp.wkt_at(t))

                    if flag:
                        print(out)
                    else:
                        print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    print(mline.wkt)
                    print(mp.wkt_at(t))

                    if flag:
                        print(out)
                    else:
                        print(1)

                    k += 1

                    eq = True

        if not eq:
            print(mline.wkt)
            print(mp.wkt_at(t))
            print(out)
        else:
            eq = False

def get_mline(MS, t):
    lines = []

    for ms in MS:
        lines += [(ms.obj_at(t))]

    return MultiLineString(lines)

#-------------------------------------------------------------------
# Create MOs functions
#-------------------------------------------------------------------

def create_moving_point(units):
    global p_linear_traj
    global pass_through_control_points

    mp = MovingPoint()

    for u in units:
        u = u.split("#")

        if len(u) == 3:
            cp0 = u[0].split(",")
            cp1 = u[1].split(",")

            intervals = u[2].split(":")

            i = intervals[0].split(",")
            i = Interval(float(i[0]), float(i[1]), True, False)

            p0 = Point(float(cp0[0]), float(cp0[1]))
            p1 = Point(float(cp1[0]), float(cp1[1]))

            msu = MPU([p0, p1], i)
            mp.add_unit(msu)
        elif len(u) == 4:
            p_linear_traj = True

            cp0 = u[0].split(",")
            cp1 = u[1].split(",")
            cp2 = u[2].split(",")
			
            intervals = u[3].split(":")

            i = intervals[0].split(",")
            i = Interval(float(i[0]), float(i[1]), True, False)

            cc = CCurve()

            p0 = Point(float(cp0[0]), float(cp0[1]))
            p1 = Point(float(cp1[0]), float(cp1[1]))
            p2 = Point(float(cp2[0]), float(cp2[1]))

            t = 0.5

            if pass_through_control_points:
                x = 2 * p1.x - t * p0.x - t * p2.x
                y = 2 * p1.y - t * p0.y - t * p2.y
                c = QuadBezierCurve(p0, Point(x, y), p2)
            else:
                c = QuadBezierCurve(p0, p1, p2)

            cc.add_curve(c, i)
            msu = MPU2(cc, i)
            mp.add_unit(msu)
        else:
            print(u)
            print("ERR: Invalid unit data.")
            sys.exit()

    return mp

#-------------------------------------------------------------------
# Time functions
#-------------------------------------------------------------------

def seconds_to_time(sec):
    day = sec / (24 * 3600)
    sec = sec % (24 * 3600)
    hour = sec / 3600

    sec %= 3600
    minutes = sec / 60

    sec %= 60
    seconds = sec

    return day, hour, minutes, seconds

def get_complementary_interval(i, it, n):
    r = []

    j = i.x
    k = i.y

    if n == 0:
        if isinstance(it, Interval):
            if j < it.x:
                r += [Interval(j, it.x, True, False)]
            if k > it.y:
                r += [Interval(it.y, k, False, True)]
        else:
            if it == j:
                r += [Interval(j, k, False, True)]
            elif it == k:
                r += [Interval(j, k, True, False)]
            else:
                r += [Interval(j, it, True, False)]
                r += [Interval(it, k, False, True)]
    elif n == 1:
        if isinstance(it, Interval):
            if j < it.x:
                r += [Interval(j, it.x, True, False)]
        else:
            if j < it:
                r += [Interval(j, it, True, False)]
    elif n == 2:
        if isinstance(it, Interval):
            if k > it.y:
                r += [Interval(it.y, k, False, True)]
        else:
            if k > it:
                r += [Interval(it, k, False, True)]

    return r

#-------------------------------------------------------------------
# Tests
#-------------------------------------------------------------------

def intersections_tests(MS, mp, initial_state, final_state, op = 1, n_linear_traj = False, ccw = False):
    global begin_exec_time
    global precision_0
    global solver_exec_time

    msegs = []

    for ms in MS:
        msegs += [create_moving_segment([ms], pass_through_control_points)]

    intersections = None
    """
    if n_linear_traj:
        for ms in msegs:    
            intersections = get_intersections_4(ms, mp, interval, intersections)
    else:
        for ms in msegs:    
            intersections = get_intersections_3(ms, mp, interval, intersections)
    """
    if n_linear_traj:
        nsegs = len(msegs)
        i = 0
        while i < nsegs:
            intersections = get_intersections_4(msegs[i], mp, interval, i, intersections)
            i += 1
    else:
        nsegs = len(msegs)
        i = 0
        while i < nsegs:
            intersections = get_intersections_3(msegs[i], mp, interval, i, intersections)
            i += 1

    if initial_state == State.Inside or initial_state == State.Touch:
        intersections = [interval.begin()] + intersections

    if final_state == State.Inside or final_state == State.Touch:
        intersections += [interval.end()]

    #a_time = time.time()
    #NI = len(intersections)
    intersections = process_intersections(intersections, mp, msegs, initial_state, final_state, ccw)
    #b_time = time.time()
    #print(b_time - a_time, NI, len(intersections))

    intersection_geom = None

    if op == Operation.Disjoint.value:
        comp = []

        N = len(intersections)

        if N == 0:
            I = Interval(interval.x, interval.y, True, True)
            comp = [I]
        else:
            t0 = intersections[0]

            if isinstance(t0, Interval):
                if t0.x > interval.x:
                    I = Interval(interval.x, t0.x, True, False)
                    comp = [I]
            else:
                if t0 > interval.x:
                    I = Interval(interval.x, t0, True, False)
                    comp = [I]

            J = 1
            
            while J < N:
                t1 = intersections[J-1]
                t2 = intersections[J]

                if isinstance(t1, Interval):
                    t1 = t1.y

                if isinstance(t2, Interval):
                    t2 = t2.x

                I = Interval(t1, t2, False, False)
                comp += [I]

                J += 1

            t0 = intersections[N-1]

            if isinstance(t0, Interval):
                if t0.y < interval.y:
                    I = Interval(t0.y, interval.y, False, True)
                    comp += [I]
            else:
                if t0 < interval.y:
                    I = Interval(t0, interval.y, False, True)
                    comp += [I]

        intersections = comp
    elif op == Operation.Within.value or op == Operation.Contains.value:
        comp = []
        N = len(intersections)

        if N > 0:
            for intersection in intersections:
                if isinstance(intersection, Interval):
                    I = Interval(intersection.x, intersection.y, False, False)
                    comp += [I]

        intersections = comp
    elif op == Operation.Touches.value:
        comp = []
        N = len(intersections)

        if N > 0:
            for intersection in intersections:
                if isinstance(intersection, Interval):
                    comp += [intersection.x, intersection.y]
                else:
                    comp += [intersection]

        intersections = comp

    end_exec_time = time.time()
    exec_time = end_exec_time - begin_exec_time

    day, hour, minutes, seconds = seconds_to_time(int(exec_time))
    sday, shour, sminutes, sseconds = seconds_to_time(int(solver_exec_time))

    NIT = len(intersections)

    """
	INTERVAL [1283.57281802375, 1806.03542794513],

	INTERVAL [1085.58931401027, 1369.91467063189],
	INTERVAL [1474.79507368380, 1864.73220066290],	

	INTERVAL [1076.52317325376, 1386.29827383020],
	INTERVAL [1422.50999353893, 1868.63710065423],	

	INTERVAL [1664.52107668254, 1795.05363836882],	

	INTERVAL [1090.51450165114, 1210.52877409407],
	INTERVAL [1508.72272437090, 1886.98914843435],	

	INTERVAL [1207.16178908481, 1263.06688900940],
	INTERVAL [1441.06949799484, 1631.20120506285],
	INTERVAL [1654.21978313411, 1804.59604141963],	

	INTERVAL [1081.33726520978, 1312.94584693599],
	INTERVAL [1322.92573683913, 1440.63549130194],
	INTERVAL [1549.81689490693, 1734.31837762386],	

	INTERVAL [1083.50378758169, 1241.89049684511],
	INTERVAL [1251.00906423320, 1305.32085938112],
	INTERVAL [1329.62653387166, 1418.98734209003],
	INTERVAL [1581.27025494226, 1662.09661352875],
	INTERVAL [1688.87630804625, 1723.03048523032],
	

    """
    """
    print('')
    for i in intersections:
        if isinstance(i, Interval):
            print(i.to_string() + ',')
        else:
            print(i, ',')
    #print('')
    """
    return NIT, exec_time, solver_exec_time, ((solver_exec_time * 100) / exec_time), seconds, sseconds

def tests(N, p_wkt, q_wkt, mpoint_st, n_linear_traj, ccw):
    op_id = [1, 2, 4, 5, 6]
    op_st = ['Intersects', 'Touches', 'Disjoint', 'Contains', 'Within']

    op_id = [1]
    op_st = ['Intersects']

    global solver_exec_times
    global solver_exec_time
    global begin_exec_time

    pass_through_control_points = True
    print_intersection_information = True
    print_solver_execution_time = True

    n_samples = 100
    interval.x = 1000
    interval.y = 2000
    epsilon = 0.0000001
    precision = '.2f'
    precision3 = '.3f'

    t0 = 1000
    t1 = 2000

    res = []

    for op in op_id:
        k = 0

        min_exec_time = sys.float_info.max
        max_exec_time = sys.float_info.min

        min_solver_exec_time = sys.float_info.max
        max_solver_exec_time = sys.float_info.min
        t_avg = 0

        while k < N:
            begin_exec_time = time.time()

            solver_exec_times = 0
            solver_exec_time = 0

            mpoint = mpoint_st

            p = loads(p_wkt)
            q = loads(q_wkt)

            reg_m_segs = get_moving_segs_from_observations(p, q, t0, t1)

            if reg_m_segs == None:
                print_error(err_code, err_msg)

            mpoint = create_moving_point([mpoint])

            initial_state, final_state = get_states(p, q, mpoint)

            NIT, exec_time, solver_exec_time, avg, sec, ssec = intersections_tests(reg_m_segs, mpoint, initial_state, final_state, op, n_linear_traj, ccw)

            min_exec_time = min(min_exec_time, exec_time)
            max_exec_time = max(max_exec_time, exec_time)

            min_solver_exec_time = min(min_solver_exec_time, solver_exec_time)
            max_solver_exec_time = max(max_solver_exec_time, solver_exec_time)

            t_avg += avg
            k += 1

        M = len(loads(p_wkt).exterior.coords) - 1

        mptt = 'L'
        if n_linear_traj:
            mptt = 'Q'

        t_avg = t_avg / N
        res += [(format(min_exec_time, precision3), format(max_exec_time, precision3), format(min_solver_exec_time, precision3), format(max_solver_exec_time, precision3), format(t_avg, precision), str(M), str(NIT), mptt)]

    return res

#-------------------------------------------------------------------
# Solvers
#-------------------------------------------------------------------

def get_solutions_quad(a0, a1, a2, it):
    global eps

    s_exec_time = time.time()

    # calculate the discriminant
    d = (a1**2) - (4*a2*a0)

    # Has no real roots
    if d < 0:
        e_exec_time = time.time()
        solver_exec_time = e_exec_time - s_exec_time
        return solver_exec_time, []

    r = []

    den = 2*a2
    d_sqrt = math.sqrt(d)

    if d == 0:
        r1 = (-a1 - d_sqrt) / den
        r = [r1]
    else:
        r1 = (-a1 - d_sqrt) / den
        r2 = (-a1 + d_sqrt) / den

        if r1 < r2:
            r = [r1, r2]
        else:
            r = [r2, r1]

    e_exec_time = time.time()
    solver_exec_time = e_exec_time - s_exec_time

    N = len(r)
    K = 0
    roots = []

    while K < N:
        if r[K] >= it.x - eps and r[K] <= it.x + eps:
            roots += [it.x]
        elif r[K] >= it.y - eps and r[K] <= it.y + eps:
            roots += [it.y]
        elif r[K] >= it.x and r[K] <= it.y:
            roots += [r[K]]

        K += 1

    return solver_exec_time, roots

def get_solutions_quartic(a, b, c, g, h, l, r, q, f, m, n, o, d, s, x, y, w, z, v, k, it):
    global eps

    s_exec_time = time.time()

    d4 = d**4
    d4k = d4*k
	
    a0 = (a*d**4*k*m - a*d**4*k*y + a*d**4*v*z + 4*a*d**3*k*m*s - 2*a*d**3*k*n*s - 2*a*d**3*k*s*y + 2*a*d**3*s*v*z + 6*a*d**2*k*m*s**2 - 6*a*d**2*k*n*s**2 + a*d**2*k*o*s**2 - a*d**2*k*s**2*y + a*d**2*s**2*v*z + 4*a*d*k*m*s**3 - 6*a*d*k*n*s**3 + 2*a*d*k*o*s**3 + a*k*m*s**4 - 2*a*k*n*s**4 + a*k*o*s**4 - 2*b*d**3*k*m*s + 2*b*d**3*k*s*y - 2*b*d**3*s*v*z - 6*b*d**2*k*m*s**2 + 4*b*d**2*k*n*s**2 + 2*b*d**2*k*s**2*y - 2*b*d**2*s**2*v*z - 6*b*d*k*m*s**3 + 8*b*d*k*n*s**3 - 2*b*d*k*o*s**3 - 2*b*k*m*s**4 + 4*b*k*n*s**4 - 2*b*k*o*s**4 + c*d**2*k*m*s**2 - c*d**2*k*s**2*y + c*d**2*s**2*v*z + 2*c*d*k*m*s**3 - 2*c*d*k*n*s**3 + c*k*m*s**4 - 2*c*k*n*s**4 + c*k*o*s**4 - d**4*g*k*r + d**4*g*k*x - d**4*g*v*w - d**4*k*m*x + d**4*k*r*y + d**4*m*v*w - d**4*r*v*z + 2*d**3*g*k*q*s - 4*d**3*g*k*r*s + 2*d**3*g*k*s*x - 2*d**3*g*s*v*w + 2*d**3*h*k*r*s - 2*d**3*h*k*s*x + 2*d**3*h*s*v*w - 2*d**3*k*m*s*x + 2*d**3*k*n*s*x - 2*d**3*k*q*s*y + 2*d**3*k*r*s*y + 2*d**3*m*s*v*w - 2*d**3*n*s*v*w + 2*d**3*q*s*v*z - 2*d**3*r*s*v*z - d**2*f*g*k*s**2 + d**2*f*k*s**2*y - d**2*f*s**2*v*z + 6*d**2*g*k*q*s**2 - 6*d**2*g*k*r*s**2 + d**2*g*k*s**2*x - d**2*g*s**2*v*w - 4*d**2*h*k*q*s**2 + 6*d**2*h*k*r*s**2 - 2*d**2*h*k*s**2*x + 2*d**2*h*s**2*v*w - d**2*k*l*r*s**2 + d**2*k*l*s**2*x - d**2*k*m*s**2*x + 2*d**2*k*n*s**2*x - d**2*k*o*s**2*x - 2*d**2*k*q*s**2*y + d**2*k*r*s**2*y - d**2*l*s**2*v*w + d**2*m*s**2*v*w - 2*d**2*n*s**2*v*w + d**2*o*s**2*v*w + 2*d**2*q*s**2*v*z - d**2*r*s**2*v*z - 2*d*f*g*k*s**3 + 2*d*f*h*k*s**3 + 6*d*g*k*q*s**3 - 4*d*g*k*r*s**3 - 8*d*h*k*q*s**3 + 6*d*h*k*r*s**3 + 2*d*k*l*q*s**3 - 2*d*k*l*r*s**3 - f*g*k*s**4 + 2*f*h*k*s**4 - f*k*l*s**4 + 2*g*k*q*s**4 - g*k*r*s**4 - 4*h*k*q*s**4 + 2*h*k*r*s**4 + 2*k*l*q*s**4 - k*l*r*s**4) / d4k
    a1 = (-a*d**4*z - 4*a*d**3*k*m + 2*a*d**3*k*n + 2*a*d**3*k*y - 2*a*d**3*s*z - 2*a*d**3*v*z - 12*a*d**2*k*m*s + 12*a*d**2*k*n*s - 2*a*d**2*k*o*s + 2*a*d**2*k*s*y - a*d**2*s**2*z - 2*a*d**2*s*v*z - 12*a*d*k*m*s**2 + 18*a*d*k*n*s**2 - 6*a*d*k*o*s**2 - 4*a*k*m*s**3 + 8*a*k*n*s**3 - 4*a*k*o*s**3 + 2*b*d**3*k*m - 2*b*d**3*k*y + 2*b*d**3*s*z + 2*b*d**3*v*z + 12*b*d**2*k*m*s - 8*b*d**2*k*n*s - 4*b*d**2*k*s*y + 2*b*d**2*s**2*z + 4*b*d**2*s*v*z + 18*b*d*k*m*s**2 - 24*b*d*k*n*s**2 + 6*b*d*k*o*s**2 + 8*b*k*m*s**3 - 16*b*k*n*s**3 + 8*b*k*o*s**3 - 2*c*d**2*k*m*s + 2*c*d**2*k*s*y - c*d**2*s**2*z - 2*c*d**2*s*v*z - 6*c*d*k*m*s**2 + 6*c*d*k*n*s**2 - 4*c*k*m*s**3 + 8*c*k*n*s**3 - 4*c*k*o*s**3 + d**4*g*w - d**4*m*w + d**4*r*z - 2*d**3*g*k*q + 4*d**3*g*k*r - 2*d**3*g*k*x + 2*d**3*g*s*w + 2*d**3*g*v*w - 2*d**3*h*k*r + 2*d**3*h*k*x - 2*d**3*h*s*w - 2*d**3*h*v*w + 2*d**3*k*m*x - 2*d**3*k*n*x + 2*d**3*k*q*y - 2*d**3*k*r*y - 2*d**3*m*s*w - 2*d**3*m*v*w + 2*d**3*n*s*w + 2*d**3*n*v*w - 2*d**3*q*s*z - 2*d**3*q*v*z + 2*d**3*r*s*z + 2*d**3*r*v*z + 2*d**2*f*g*k*s - 2*d**2*f*k*s*y + d**2*f*s**2*z + 2*d**2*f*s*v*z - 12*d**2*g*k*q*s + 12*d**2*g*k*r*s - 2*d**2*g*k*s*x + d**2*g*s**2*w + 2*d**2*g*s*v*w + 8*d**2*h*k*q*s - 12*d**2*h*k*r*s + 4*d**2*h*k*s*x - 2*d**2*h*s**2*w - 4*d**2*h*s*v*w + 2*d**2*k*l*r*s - 2*d**2*k*l*s*x + 2*d**2*k*m*s*x - 4*d**2*k*n*s*x + 2*d**2*k*o*s*x + 4*d**2*k*q*s*y - 2*d**2*k*r*s*y + d**2*l*s**2*w + 2*d**2*l*s*v*w - d**2*m*s**2*w - 2*d**2*m*s*v*w + 2*d**2*n*s**2*w + 4*d**2*n*s*v*w - d**2*o*s**2*w - 2*d**2*o*s*v*w - 2*d**2*q*s**2*z - 4*d**2*q*s*v*z + d**2*r*s**2*z + 2*d**2*r*s*v*z + 6*d*f*g*k*s**2 - 6*d*f*h*k*s**2 - 18*d*g*k*q*s**2 + 12*d*g*k*r*s**2 + 24*d*h*k*q*s**2 - 18*d*h*k*r*s**2 - 6*d*k*l*q*s**2 + 6*d*k*l*r*s**2 + 4*f*g*k*s**3 - 8*f*h*k*s**3 + 4*f*k*l*s**3 - 8*g*k*q*s**3 + 4*g*k*r*s**3 + 16*h*k*q*s**3 - 8*h*k*r*s**3 - 8*k*l*q*s**3 + 4*k*l*r*s**3 ) / d4k
    a2 = (2*a*d**3*z + 6*a*d**2*k*m - 6*a*d**2*k*n + a*d**2*k*o - a*d**2*k*y + 2*a*d**2*s*z + a*d**2*v*z + 12*a*d*k*m*s - 18*a*d*k*n*s + 6*a*d*k*o*s + 6*a*k*m*s**2 - 12*a*k*n*s**2 + 6*a*k*o*s**2 - 2*b*d**3*z - 6*b*d**2*k*m + 4*b*d**2*k*n + 2*b*d**2*k*y - 4*b*d**2*s*z - 2*b*d**2*v*z - 18*b*d*k*m*s + 24*b*d*k*n*s - 6*b*d*k*o*s - 12*b*k*m*s**2 + 24*b*k*n*s**2 - 12*b*k*o*s**2 + c*d**2*k*m - c*d**2*k*y + 2*c*d**2*s*z + c*d**2*v*z + 6*c*d*k*m*s - 6*c*d*k*n*s + 6*c*k*m*s**2 - 12*c*k*n*s**2 + 6*c*k*o*s**2 - 2*d**3*g*w + 2*d**3*h*w + 2*d**3*m*w - 2*d**3*n*w + 2*d**3*q*z - 2*d**3*r*z - d**2*f*g*k + d**2*f*k*y - 2*d**2*f*s*z - d**2*f*v*z + 6*d**2*g*k*q - 6*d**2*g*k*r + d**2*g*k*x - 2*d**2*g*s*w - d**2*g*v*w - 4*d**2*h*k*q + 6*d**2*h*k*r - 2*d**2*h*k*x + 4*d**2*h*s*w + 2*d**2*h*v*w - d**2*k*l*r + d**2*k*l*x - d**2*k*m*x + 2*d**2*k*n*x - d**2*k*o*x - 2*d**2*k*q*y + d**2*k*r*y - 2*d**2*l*s*w - d**2*l*v*w + 2*d**2*m*s*w + d**2*m*v*w - 4*d**2*n*s*w - 2*d**2*n*v*w + 2*d**2*o*s*w + d**2*o*v*w + 4*d**2*q*s*z + 2*d**2*q*v*z - 2*d**2*r*s*z - d**2*r*v*z - 6*d*f*g*k*s + 6*d*f*h*k*s + 18*d*g*k*q*s - 12*d*g*k*r*s - 24*d*h*k*q*s + 18*d*h*k*r*s + 6*d*k*l*q*s - 6*d*k*l*r*s - 6*f*g*k*s**2 + 12*f*h*k*s**2 - 6*f*k*l*s**2 + 12*g*k*q*s**2 - 6*g*k*r*s**2 - 24*h*k*q*s**2 + 12*h*k*r*s**2 + 12*k*l*q*s**2 - 6*k*l*r*s**2 ) / d4k
    a3 = (-a*d**2*z - 4*a*d*k*m + 6*a*d*k*n - 2*a*d*k*o - 4*a*k*m*s + 8*a*k*n*s - 4*a*k*o*s + 2*b*d**2*z + 6*b*d*k*m - 8*b*d*k*n + 2*b*d*k*o + 8*b*k*m*s - 16*b*k*n*s + 8*b*k*o*s - c*d**2*z - 2*c*d*k*m + 2*c*d*k*n - 4*c*k*m*s + 8*c*k*n*s - 4*c*k*o*s + d**2*f*z + d**2*g*w - 2*d**2*h*w + d**2*l*w - d**2*m*w + 2*d**2*n*w - d**2*o*w - 2*d**2*q*z + d**2*r*z + 2*d*f*g*k - 2*d*f*h*k - 6*d*g*k*q + 4*d*g*k*r + 8*d*h*k*q - 6*d*h*k*r - 2*d*k*l*q + 2*d*k*l*r + 4*f*g*k*s - 8*f*h*k*s + 4*f*k*l*s - 8*g*k*q*s + 4*g*k*r*s + 16*h*k*q*s - 8*h*k*r*s - 8*k*l*q*s + 4*k*l*r*s ) / d4k
    a4 = (a*k*m - 2*a*k*n + a*k*o - 2*b*k*m + 4*b*k*n - 2*b*k*o + c*k*m - 2*c*k*n + c*k*o - f*g*k + 2*f*h*k - f*k*l + 2*g*k*q - g*k*r - 4*h*k*q + 2*h*k*r + 2*k*l*q - k*l*r ) / d4k

    coeff = [a4, a3, a2, a1, a0]

    r = np.roots(coeff)

    N = len(r)
    K = 0

    rroots = []

    while K < N:
        v = r[K]

        if im(v) == 0:
            v = re(v)
            if v >= it.x - eps and v <= it.x + eps:
                rroots += [it.x]
            elif v >= it.y - eps and v <= it.y + eps:
                rroots += [it.y]
            elif v >= it.x and v <= it.y:
                rroots += [v]

        K += 1

    rroots.sort()

    e_exec_time = time.time()
    _exec_time = e_exec_time - s_exec_time

    return _exec_time, rroots

#@numba.jit(nopython=True, parallel=True)
#@jit(nopython=True)
def get_solutions_quartic2(a, b, c, g, h, l, r, q, f, m, n, o, d, s, w, v, y, x, k, u, z, p, it):
    global eps

    s_exec_time = time.time()

    #d2 = d*d
    #ddd = d2*d
    #dddd = ddd*d #d**4

    """
    a0 = (2*a*dddd*k*p*z + 2*a*dddd*k*z**2 + a*dddd*m*p**2 - a*dddd*p**2*x - 2*a*dddd*p*x*z - a*dddd*u*z**2 - a*dddd*x*z**2 + 4*a*ddd*k*p*s*z + 4*a*ddd*k*s*z**2 + 4*a*ddd*m*p**2*s - 2*a*ddd*n*p**2*s - 2*a*ddd*p**2*s*x - 4*a*ddd*p*s*x*z - 2*a*ddd*s*u*z**2 - 2*a*ddd*s*x*z**2 + 2*a*d2*k*p*s**2*z + 2*a*d2*k*s**2*z**2 + 6*a*d2*m*p**2*s**2 - 6*a*d2*n*p**2*s**2 + a*d2*o*p**2*s**2 - a*d2*p**2*s**2*x - 2*a*d2*p*s**2*x*z - a*d2*s**2*u*z**2 - a*d2*s**2*x*z**2 + 4*a*d*m*p**2*s**3 - 6*a*d*n*p**2*s**3 + 2*a*d*o*p**2*s**3 + a*m*p**2*s**4 - 2*a*n*p**2*s**4 + a*o*p**2*s**4 - 4*b*ddd*k*p*s*z - 4*b*ddd*k*s*z**2 - 2*b*ddd*m*p**2*s + 2*b*ddd*p**2*s*x + 4*b*ddd*p*s*x*z + 2*b*ddd*s*u*z**2 + 2*b*ddd*s*x*z**2 - 4*b*d2*k*p*s**2*z - 4*b*d2*k*s**2*z**2 - 6*b*d2*m*p**2*s**2 + 4*b*d2*n*p**2*s**2 + 2*b*d2*p**2*s**2*x + 4*b*d2*p*s**2*x*z + 2*b*d2*s**2*u*z**2 + 2*b*d2*s**2*x*z**2 - 6*b*d*m*p**2*s**3 + 8*b*d*n*p**2*s**3 - 2*b*d*o*p**2*s**3 - 2*b*m*p**2*s**4 + 4*b*n*p**2*s**4 - 2*b*o*p**2*s**4 + 2*c*d2*k*p*s**2*z + 2*c*d2*k*s**2*z**2 + c*d2*m*p**2*s**2 - c*d2*p**2*s**2*x - 2*c*d2*p*s**2*x*z - c*d2*s**2*u*z**2 - c*d2*s**2*x*z**2 + 2*c*d*m*p**2*s**3 - 2*c*d*n*p**2*s**3 + c*m*p**2*s**4 - 2*c*n*p**2*s**4 + c*o*p**2*s**4 - dddd*g*p**2*r + dddd*g*p**2*w - 2*dddd*g*p*v*z + 2*dddd*g*p*w*z - 2*dddd*g*v*z**2 + dddd*g*w*z**2 + dddd*g*y*z**2 - 2*dddd*k*p*r*z - 2*dddd*k*r*z**2 - dddd*m*p**2*w + 2*dddd*m*p*v*z - 2*dddd*m*p*w*z + 2*dddd*m*v*z**2 - dddd*m*w*z**2 - dddd*m*y*z**2 + dddd*p**2*r*x + 2*dddd*p*r*x*z + dddd*r*u*z**2 + dddd*r*x*z**2 + 2*ddd*g*p**2*q*s - 4*ddd*g*p**2*r*s + 2*ddd*g*p**2*s*w - 4*ddd*g*p*s*v*z + 4*ddd*g*p*s*w*z - 4*ddd*g*s*v*z**2 + 2*ddd*g*s*w*z**2 + 2*ddd*g*s*y*z**2 + 2*ddd*h*p**2*r*s - 2*ddd*h*p**2*s*w + 4*ddd*h*p*s*v*z - 4*ddd*h*p*s*w*z + 4*ddd*h*s*v*z**2 - 2*ddd*h*s*w*z**2 - 2*ddd*h*s*y*z**2 + 4*ddd*k*p*q*s*z - 4*ddd*k*p*r*s*z + 4*ddd*k*q*s*z**2 - 4*ddd*k*r*s*z**2 - 2*ddd*m*p**2*s*w + 4*ddd*m*p*s*v*z - 4*ddd*m*p*s*w*z + 4*ddd*m*s*v*z**2 - 2*ddd*m*s*w*z**2 - 2*ddd*m*s*y*z**2 + 2*ddd*n*p**2*s*w - 4*ddd*n*p*s*v*z + 4*ddd*n*p*s*w*z - 4*ddd*n*s*v*z**2 + 2*ddd*n*s*w*z**2 + 2*ddd*n*s*y*z**2 - 2*ddd*p**2*q*s*x + 2*ddd*p**2*r*s*x - 4*ddd*p*q*s*x*z + 4*ddd*p*r*s*x*z - 2*ddd*q*s*u*z**2 - 2*ddd*q*s*x*z**2 + 2*ddd*r*s*u*z**2 + 2*ddd*r*s*x*z**2 - d2*f*g*p**2*s**2 - 2*d2*f*k*p*s**2*z - 2*d2*f*k*s**2*z**2 + d2*f*p**2*s**2*x + 2*d2*f*p*s**2*x*z + d2*f*s**2*u*z**2 + d2*f*s**2*x*z**2 + 6*d2*g*p**2*q*s**2 - 6*d2*g*p**2*r*s**2 + d2*g*p**2*s**2*w - 2*d2*g*p*s**2*v*z + 2*d2*g*p*s**2*w*z - 2*d2*g*s**2*v*z**2 + d2*g*s**2*w*z**2 + d2*g*s**2*y*z**2 - 4*d2*h*p**2*q*s**2 + 6*d2*h*p**2*r*s**2 - 2*d2*h*p**2*s**2*w + 4*d2*h*p*s**2*v*z - 4*d2*h*p*s**2*w*z + 4*d2*h*s**2*v*z**2 - 2*d2*h*s**2*w*z**2 - 2*d2*h*s**2*y*z**2 + 4*d2*k*p*q*s**2*z - 2*d2*k*p*r*s**2*z + 4*d2*k*q*s**2*z**2 - 2*d2*k*r*s**2*z**2 - d2*l*p**2*r*s**2 + d2*l*p**2*s**2*w - 2*d2*l*p*s**2*v*z + 2*d2*l*p*s**2*w*z - 2*d2*l*s**2*v*z**2 + d2*l*s**2*w*z**2 + d2*l*s**2*y*z**2 - d2*m*p**2*s**2*w + 2*d2*m*p*s**2*v*z - 2*d2*m*p*s**2*w*z + 2*d2*m*s**2*v*z**2 - d2*m*s**2*w*z**2 - d2*m*s**2*y*z**2 + 2*d2*n*p**2*s**2*w - 4*d2*n*p*s**2*v*z + 4*d2*n*p*s**2*w*z - 4*d2*n*s**2*v*z**2 + 2*d2*n*s**2*w*z**2 + 2*d2*n*s**2*y*z**2 - d2*o*p**2*s**2*w + 2*d2*o*p*s**2*v*z - 2*d2*o*p*s**2*w*z + 2*d2*o*s**2*v*z**2 - d2*o*s**2*w*z**2 - d2*o*s**2*y*z**2 - 2*d2*p**2*q*s**2*x + d2*p**2*r*s**2*x - 4*d2*p*q*s**2*x*z + 2*d2*p*r*s**2*x*z - 2*d2*q*s**2*u*z**2 - 2*d2*q*s**2*x*z**2 + d2*r*s**2*u*z**2 + d2*r*s**2*x*z**2 - 2*d*f*g*p**2*s**3 + 2*d*f*h*p**2*s**3 + 6*d*g*p**2*q*s**3 - 4*d*g*p**2*r*s**3 - 8*d*h*p**2*q*s**3 + 6*d*h*p**2*r*s**3 + 2*d*l*p**2*q*s**3 - 2*d*l*p**2*r*s**3 - f*g*p**2*s**4 + 2*f*h*p**2*s**4 - f*l*p**2*s**4 + 2*g*p**2*q*s**4 - g*p**2*r*s**4 - 4*h*p**2*q*s**4 + 2*h*p**2*r*s**4 + 2*l*p**2*q*s**4 - l*p**2*r*s**4 ) / (dddd*p**2)
    a1 = (-2*a*dddd*k*p - 4*a*dddd*k*z + 2*a*dddd*p*x + 2*a*dddd*u*z + 2*a*dddd*x*z - 4*a*ddd*k*p*s - 4*a*ddd*k*p*z - 8*a*ddd*k*s*z - 4*a*ddd*k*z**2 - 4*a*ddd*m*p**2 + 2*a*ddd*n*p**2 + 2*a*ddd*p**2*x + 4*a*ddd*p*s*x + 4*a*ddd*p*x*z + 4*a*ddd*s*u*z + 4*a*ddd*s*x*z + 2*a*ddd*u*z**2 + 2*a*ddd*x*z**2 - 2*a*d2*k*p*s**2 - 4*a*d2*k*p*s*z - 4*a*d2*k*s**2*z - 4*a*d2*k*s*z**2 - 12*a*d2*m*p**2*s + 12*a*d2*n*p**2*s - 2*a*d2*o*p**2*s + 2*a*d2*p**2*s*x + 2*a*d2*p*s**2*x + 4*a*d2*p*s*x*z + 2*a*d2*s**2*u*z + 2*a*d2*s**2*x*z + 2*a*d2*s*u*z**2 + 2*a*d2*s*x*z**2 - 12*a*d*m*p**2*s**2 + 18*a*d*n*p**2*s**2 - 6*a*d*o*p**2*s**2 - 4*a*m*p**2*s**3 + 8*a*n*p**2*s**3 - 4*a*o*p**2*s**3 + 4*b*ddd*k*p*s + 4*b*ddd*k*p*z + 8*b*ddd*k*s*z + 4*b*ddd*k*z**2 + 2*b*ddd*m*p**2 - 2*b*ddd*p**2*x - 4*b*ddd*p*s*x - 4*b*ddd*p*x*z - 4*b*ddd*s*u*z - 4*b*ddd*s*x*z - 2*b*ddd*u*z**2 - 2*b*ddd*x*z**2 + 4*b*d2*k*p*s**2 + 8*b*d2*k*p*s*z + 8*b*d2*k*s**2*z + 8*b*d2*k*s*z**2 + 12*b*d2*m*p**2*s - 8*b*d2*n*p**2*s - 4*b*d2*p**2*s*x - 4*b*d2*p*s**2*x - 8*b*d2*p*s*x*z - 4*b*d2*s**2*u*z - 4*b*d2*s**2*x*z - 4*b*d2*s*u*z**2 - 4*b*d2*s*x*z**2 + 18*b*d*m*p**2*s**2 - 24*b*d*n*p**2*s**2 + 6*b*d*o*p**2*s**2 + 8*b*m*p**2*s**3 - 16*b*n*p**2*s**3 + 8*b*o*p**2*s**3 - 2*c*d2*k*p*s**2 - 4*c*d2*k*p*s*z - 4*c*d2*k*s**2*z - 4*c*d2*k*s*z**2 - 2*c*d2*m*p**2*s + 2*c*d2*p**2*s*x + 2*c*d2*p*s**2*x + 4*c*d2*p*s*x*z + 2*c*d2*s**2*u*z + 2*c*d2*s**2*x*z + 2*c*d2*s*u*z**2 + 2*c*d2*s*x*z**2 - 6*c*d*m*p**2*s**2 + 6*c*d*n*p**2*s**2 - 4*c*m*p**2*s**3 + 8*c*n*p**2*s**3 - 4*c*o*p**2*s**3 + 2*dddd*g*p*v - 2*dddd*g*p*w + 4*dddd*g*v*z - 2*dddd*g*w*z - 2*dddd*g*y*z + 2*dddd*k*p*r + 4*dddd*k*r*z - 2*dddd*m*p*v + 2*dddd*m*p*w - 4*dddd*m*v*z + 2*dddd*m*w*z + 2*dddd*m*y*z - 2*dddd*p*r*x - 2*dddd*r*u*z - 2*dddd*r*x*z - 2*ddd*g*p**2*q + 4*ddd*g*p**2*r - 2*ddd*g*p**2*w + 4*ddd*g*p*s*v - 4*ddd*g*p*s*w + 4*ddd*g*p*v*z - 4*ddd*g*p*w*z + 8*ddd*g*s*v*z - 4*ddd*g*s*w*z - 4*ddd*g*s*y*z + 4*ddd*g*v*z**2 - 2*ddd*g*w*z**2 - 2*ddd*g*y*z**2 - 2*ddd*h*p**2*r + 2*ddd*h*p**2*w - 4*ddd*h*p*s*v + 4*ddd*h*p*s*w - 4*ddd*h*p*v*z + 4*ddd*h*p*w*z - 8*ddd*h*s*v*z + 4*ddd*h*s*w*z + 4*ddd*h*s*y*z - 4*ddd*h*v*z**2 + 2*ddd*h*w*z**2 + 2*ddd*h*y*z**2 - 4*ddd*k*p*q*s - 4*ddd*k*p*q*z + 4*ddd*k*p*r*s + 4*ddd*k*p*r*z - 8*ddd*k*q*s*z - 4*ddd*k*q*z**2 + 8*ddd*k*r*s*z + 4*ddd*k*r*z**2 + 2*ddd*m*p**2*w - 4*ddd*m*p*s*v + 4*ddd*m*p*s*w - 4*ddd*m*p*v*z + 4*ddd*m*p*w*z - 8*ddd*m*s*v*z + 4*ddd*m*s*w*z + 4*ddd*m*s*y*z - 4*ddd*m*v*z**2 + 2*ddd*m*w*z**2 + 2*ddd*m*y*z**2 - 2*ddd*n*p**2*w + 4*ddd*n*p*s*v - 4*ddd*n*p*s*w + 4*ddd*n*p*v*z - 4*ddd*n*p*w*z + 8*ddd*n*s*v*z - 4*ddd*n*s*w*z - 4*ddd*n*s*y*z + 4*ddd*n*v*z**2 - 2*ddd*n*w*z**2 - 2*ddd*n*y*z**2 + 2*ddd*p**2*q*x - 2*ddd*p**2*r*x + 4*ddd*p*q*s*x + 4*ddd*p*q*x*z - 4*ddd*p*r*s*x - 4*ddd*p*r*x*z + 4*ddd*q*s*u*z + 4*ddd*q*s*x*z + 2*ddd*q*u*z**2 + 2*ddd*q*x*z**2 - 4*ddd*r*s*u*z - 4*ddd*r*s*x*z - 2*ddd*r*u*z**2 - 2*ddd*r*x*z**2 + 2*d2*f*g*p**2*s + 2*d2*f*k*p*s**2 + 4*d2*f*k*p*s*z + 4*d2*f*k*s**2*z + 4*d2*f*k*s*z**2 - 2*d2*f*p**2*s*x - 2*d2*f*p*s**2*x - 4*d2*f*p*s*x*z - 2*d2*f*s**2*u*z - 2*d2*f*s**2*x*z - 2*d2*f*s*u*z**2 - 2*d2*f*s*x*z**2 - 12*d2*g*p**2*q*s + 12*d2*g*p**2*r*s - 2*d2*g*p**2*s*w + 2*d2*g*p*s**2*v - 2*d2*g*p*s**2*w + 4*d2*g*p*s*v*z - 4*d2*g*p*s*w*z + 4*d2*g*s**2*v*z - 2*d2*g*s**2*w*z - 2*d2*g*s**2*y*z + 4*d2*g*s*v*z**2 - 2*d2*g*s*w*z**2 - 2*d2*g*s*y*z**2 + 8*d2*h*p**2*q*s - 12*d2*h*p**2*r*s + 4*d2*h*p**2*s*w - 4*d2*h*p*s**2*v + 4*d2*h*p*s**2*w - 8*d2*h*p*s*v*z + 8*d2*h*p*s*w*z - 8*d2*h*s**2*v*z + 4*d2*h*s**2*w*z + 4*d2*h*s**2*y*z - 8*d2*h*s*v*z**2 + 4*d2*h*s*w*z**2 + 4*d2*h*s*y*z**2 - 4*d2*k*p*q*s**2 - 8*d2*k*p*q*s*z + 2*d2*k*p*r*s**2 + 4*d2*k*p*r*s*z - 8*d2*k*q*s**2*z - 8*d2*k*q*s*z**2 + 4*d2*k*r*s**2*z + 4*d2*k*r*s*z**2 + 2*d2*l*p**2*r*s - 2*d2*l*p**2*s*w + 2*d2*l*p*s**2*v - 2*d2*l*p*s**2*w + 4*d2*l*p*s*v*z - 4*d2*l*p*s*w*z + 4*d2*l*s**2*v*z - 2*d2*l*s**2*w*z - 2*d2*l*s**2*y*z + 4*d2*l*s*v*z**2 - 2*d2*l*s*w*z**2 - 2*d2*l*s*y*z**2 + 2*d2*m*p**2*s*w - 2*d2*m*p*s**2*v + 2*d2*m*p*s**2*w - 4*d2*m*p*s*v*z + 4*d2*m*p*s*w*z - 4*d2*m*s**2*v*z + 2*d2*m*s**2*w*z + 2*d2*m*s**2*y*z - 4*d2*m*s*v*z**2 + 2*d2*m*s*w*z**2 + 2*d2*m*s*y*z**2 - 4*d2*n*p**2*s*w + 4*d2*n*p*s**2*v - 4*d2*n*p*s**2*w + 8*d2*n*p*s*v*z - 8*d2*n*p*s*w*z + 8*d2*n*s**2*v*z - 4*d2*n*s**2*w*z - 4*d2*n*s**2*y*z + 8*d2*n*s*v*z**2 - 4*d2*n*s*w*z**2 - 4*d2*n*s*y*z**2 + 2*d2*o*p**2*s*w - 2*d2*o*p*s**2*v + 2*d2*o*p*s**2*w - 4*d2*o*p*s*v*z + 4*d2*o*p*s*w*z - 4*d2*o*s**2*v*z + 2*d2*o*s**2*w*z + 2*d2*o*s**2*y*z - 4*d2*o*s*v*z**2 + 2*d2*o*s*w*z**2 + 2*d2*o*s*y*z**2 + 4*d2*p**2*q*s*x - 2*d2*p**2*r*s*x + 4*d2*p*q*s**2*x + 8*d2*p*q*s*x*z - 2*d2*p*r*s**2*x - 4*d2*p*r*s*x*z + 4*d2*q*s**2*u*z + 4*d2*q*s**2*x*z + 4*d2*q*s*u*z**2 + 4*d2*q*s*x*z**2 - 2*d2*r*s**2*u*z - 2*d2*r*s**2*x*z - 2*d2*r*s*u*z**2 - 2*d2*r*s*x*z**2 + 6*d*f*g*p**2*s**2 - 6*d*f*h*p**2*s**2 - 18*d*g*p**2*q*s**2 + 12*d*g*p**2*r*s**2 + 24*d*h*p**2*q*s**2 - 18*d*h*p**2*r*s**2 - 6*d*l*p**2*q*s**2 + 6*d*l*p**2*r*s**2 + 4*f*g*p**2*s**3 - 8*f*h*p**2*s**3 + 4*f*l*p**2*s**3 - 8*g*p**2*q*s**3 + 4*g*p**2*r*s**3 + 16*h*p**2*q*s**3 - 8*h*p**2*r*s**3 - 8*l*p**2*q*s**3 + 4*l*p**2*r*s**3 ) / (dddd*p**2)
    a2 = (2*a*dddd*k - a*dddd*u - a*dddd*x + 4*a*ddd*k*p + 4*a*ddd*k*s + 8*a*ddd*k*z - 4*a*ddd*p*x - 2*a*ddd*s*u - 2*a*ddd*s*x - 4*a*ddd*u*z - 4*a*ddd*x*z + 4*a*d2*k*p*s + 2*a*d2*k*p*z + 2*a*d2*k*s**2 + 8*a*d2*k*s*z + 2*a*d2*k*z**2 + 6*a*d2*m*p**2 - 6*a*d2*n*p**2 + a*d2*o*p**2 - a*d2*p**2*x - 4*a*d2*p*s*x - 2*a*d2*p*x*z - a*d2*s**2*u - a*d2*s**2*x - 4*a*d2*s*u*z - 4*a*d2*s*x*z - a*d2*u*z**2 - a*d2*x*z**2 + 12*a*d*m*p**2*s - 18*a*d*n*p**2*s + 6*a*d*o*p**2*s + 6*a*m*p**2*s**2 - 12*a*n*p**2*s**2 + 6*a*o*p**2*s**2 - 4*b*ddd*k*p - 4*b*ddd*k*s - 8*b*ddd*k*z + 4*b*ddd*p*x + 2*b*ddd*s*u + 2*b*ddd*s*x + 4*b*ddd*u*z + 4*b*ddd*x*z - 8*b*d2*k*p*s - 4*b*d2*k*p*z - 4*b*d2*k*s**2 - 16*b*d2*k*s*z - 4*b*d2*k*z**2 - 6*b*d2*m*p**2 + 4*b*d2*n*p**2 + 2*b*d2*p**2*x + 8*b*d2*p*s*x + 4*b*d2*p*x*z + 2*b*d2*s**2*u + 2*b*d2*s**2*x + 8*b*d2*s*u*z + 8*b*d2*s*x*z + 2*b*d2*u*z**2 + 2*b*d2*x*z**2 - 18*b*d*m*p**2*s + 24*b*d*n*p**2*s - 6*b*d*o*p**2*s - 12*b*m*p**2*s**2 + 24*b*n*p**2*s**2 - 12*b*o*p**2*s**2 + 4*c*d2*k*p*s + 2*c*d2*k*p*z + 2*c*d2*k*s**2 + 8*c*d2*k*s*z + 2*c*d2*k*z**2 + c*d2*m*p**2 - c*d2*p**2*x - 4*c*d2*p*s*x - 2*c*d2*p*x*z - c*d2*s**2*u - c*d2*s**2*x - 4*c*d2*s*u*z - 4*c*d2*s*x*z - c*d2*u*z**2 - c*d2*x*z**2 + 6*c*d*m*p**2*s - 6*c*d*n*p**2*s + 6*c*m*p**2*s**2 - 12*c*n*p**2*s**2 + 6*c*o*p**2*s**2 - 2*dddd*g*v + dddd*g*w + dddd*g*y - 2*dddd*k*r + 2*dddd*m*v - dddd*m*w - dddd*m*y + dddd*r*u + dddd*r*x - 4*ddd*g*p*v + 4*ddd*g*p*w - 4*ddd*g*s*v + 2*ddd*g*s*w + 2*ddd*g*s*y - 8*ddd*g*v*z + 4*ddd*g*w*z + 4*ddd*g*y*z + 4*ddd*h*p*v - 4*ddd*h*p*w + 4*ddd*h*s*v - 2*ddd*h*s*w - 2*ddd*h*s*y + 8*ddd*h*v*z - 4*ddd*h*w*z - 4*ddd*h*y*z + 4*ddd*k*p*q - 4*ddd*k*p*r + 4*ddd*k*q*s + 8*ddd*k*q*z - 4*ddd*k*r*s - 8*ddd*k*r*z + 4*ddd*m*p*v - 4*ddd*m*p*w + 4*ddd*m*s*v - 2*ddd*m*s*w - 2*ddd*m*s*y + 8*ddd*m*v*z - 4*ddd*m*w*z - 4*ddd*m*y*z - 4*ddd*n*p*v + 4*ddd*n*p*w - 4*ddd*n*s*v + 2*ddd*n*s*w + 2*ddd*n*s*y - 8*ddd*n*v*z + 4*ddd*n*w*z + 4*ddd*n*y*z - 4*ddd*p*q*x + 4*ddd*p*r*x - 2*ddd*q*s*u - 2*ddd*q*s*x - 4*ddd*q*u*z - 4*ddd*q*x*z + 2*ddd*r*s*u + 2*ddd*r*s*x + 4*ddd*r*u*z + 4*ddd*r*x*z - d2*f*g*p**2 - 4*d2*f*k*p*s - 2*d2*f*k*p*z - 2*d2*f*k*s**2 - 8*d2*f*k*s*z - 2*d2*f*k*z**2 + d2*f*p**2*x + 4*d2*f*p*s*x + 2*d2*f*p*x*z + d2*f*s**2*u + d2*f*s**2*x + 4*d2*f*s*u*z + 4*d2*f*s*x*z + d2*f*u*z**2 + d2*f*x*z**2 + 6*d2*g*p**2*q - 6*d2*g*p**2*r + d2*g*p**2*w - 4*d2*g*p*s*v + 4*d2*g*p*s*w - 2*d2*g*p*v*z + 2*d2*g*p*w*z - 2*d2*g*s**2*v + d2*g*s**2*w + d2*g*s**2*y - 8*d2*g*s*v*z + 4*d2*g*s*w*z + 4*d2*g*s*y*z - 2*d2*g*v*z**2 + d2*g*w*z**2 + d2*g*y*z**2 - 4*d2*h*p**2*q + 6*d2*h*p**2*r - 2*d2*h*p**2*w + 8*d2*h*p*s*v - 8*d2*h*p*s*w + 4*d2*h*p*v*z - 4*d2*h*p*w*z + 4*d2*h*s**2*v - 2*d2*h*s**2*w - 2*d2*h*s**2*y + 16*d2*h*s*v*z - 8*d2*h*s*w*z - 8*d2*h*s*y*z + 4*d2*h*v*z**2 - 2*d2*h*w*z**2 - 2*d2*h*y*z**2 + 8*d2*k*p*q*s + 4*d2*k*p*q*z - 4*d2*k*p*r*s - 2*d2*k*p*r*z + 4*d2*k*q*s**2 + 16*d2*k*q*s*z + 4*d2*k*q*z**2 - 2*d2*k*r*s**2 - 8*d2*k*r*s*z - 2*d2*k*r*z**2 - d2*l*p**2*r + d2*l*p**2*w - 4*d2*l*p*s*v + 4*d2*l*p*s*w - 2*d2*l*p*v*z + 2*d2*l*p*w*z - 2*d2*l*s**2*v + d2*l*s**2*w + d2*l*s**2*y - 8*d2*l*s*v*z + 4*d2*l*s*w*z + 4*d2*l*s*y*z - 2*d2*l*v*z**2 + d2*l*w*z**2 + d2*l*y*z**2 - d2*m*p**2*w + 4*d2*m*p*s*v - 4*d2*m*p*s*w + 2*d2*m*p*v*z - 2*d2*m*p*w*z + 2*d2*m*s**2*v - d2*m*s**2*w - d2*m*s**2*y + 8*d2*m*s*v*z - 4*d2*m*s*w*z - 4*d2*m*s*y*z + 2*d2*m*v*z**2 - d2*m*w*z**2 - d2*m*y*z**2 + 2*d2*n*p**2*w - 8*d2*n*p*s*v + 8*d2*n*p*s*w - 4*d2*n*p*v*z + 4*d2*n*p*w*z - 4*d2*n*s**2*v + 2*d2*n*s**2*w + 2*d2*n*s**2*y - 16*d2*n*s*v*z + 8*d2*n*s*w*z + 8*d2*n*s*y*z - 4*d2*n*v*z**2 + 2*d2*n*w*z**2 + 2*d2*n*y*z**2 - d2*o*p**2*w + 4*d2*o*p*s*v - 4*d2*o*p*s*w + 2*d2*o*p*v*z - 2*d2*o*p*w*z + 2*d2*o*s**2*v - d2*o*s**2*w - d2*o*s**2*y + 8*d2*o*s*v*z - 4*d2*o*s*w*z - 4*d2*o*s*y*z + 2*d2*o*v*z**2 - d2*o*w*z**2 - d2*o*y*z**2 - 2*d2*p**2*q*x + d2*p**2*r*x - 8*d2*p*q*s*x - 4*d2*p*q*x*z + 4*d2*p*r*s*x + 2*d2*p*r*x*z - 2*d2*q*s**2*u - 2*d2*q*s**2*x - 8*d2*q*s*u*z - 8*d2*q*s*x*z - 2*d2*q*u*z**2 - 2*d2*q*x*z**2 + d2*r*s**2*u + d2*r*s**2*x + 4*d2*r*s*u*z + 4*d2*r*s*x*z + d2*r*u*z**2 + d2*r*x*z**2 - 6*d*f*g*p**2*s + 6*d*f*h*p**2*s + 18*d*g*p**2*q*s - 12*d*g*p**2*r*s - 24*d*h*p**2*q*s + 18*d*h*p**2*r*s + 6*d*l*p**2*q*s - 6*d*l*p**2*r*s - 6*f*g*p**2*s**2 + 12*f*h*p**2*s**2 - 6*f*l*p**2*s**2 + 12*g*p**2*q*s**2 - 6*g*p**2*r*s**2 - 24*h*p**2*q*s**2 + 12*h*p**2*r*s**2 + 12*l*p**2*q*s**2 - 6*l*p**2*r*s**2 ) / (dddd*p**2)
    a3 = (-4*a*ddd*k + 2*a*ddd*u + 2*a*ddd*x - 2*a*d2*k*p - 4*a*d2*k*s - 4*a*d2*k*z + 2*a*d2*p*x + 2*a*d2*s*u + 2*a*d2*s*x + 2*a*d2*u*z + 2*a*d2*x*z - 4*a*d*m*p**2 + 6*a*d*n*p**2 - 2*a*d*o*p**2 - 4*a*m*p**2*s + 8*a*n*p**2*s - 4*a*o*p**2*s + 4*b*ddd*k - 2*b*ddd*u - 2*b*ddd*x + 4*b*d2*k*p + 8*b*d2*k*s + 8*b*d2*k*z - 4*b*d2*p*x - 4*b*d2*s*u - 4*b*d2*s*x - 4*b*d2*u*z - 4*b*d2*x*z + 6*b*d*m*p**2 - 8*b*d*n*p**2 + 2*b*d*o*p**2 + 8*b*m*p**2*s - 16*b*n*p**2*s + 8*b*o*p**2*s - 2*c*d2*k*p - 4*c*d2*k*s - 4*c*d2*k*z + 2*c*d**2*p*x + 2*c*d**2*s*u + 2*c*d**2*s*x + 2*c*d**2*u*z + 2*c*d**2*x*z - 2*c*d*m*p**2 + 2*c*d*n*p**2 - 4*c*m*p**2*s + 8*c*n*p**2*s - 4*c*o*p**2*s + 4*ddd*g*v - 2*ddd*g*w - 2*ddd*g*y - 4*ddd*h*v + 2*ddd*h*w + 2*ddd*h*y - 4*ddd*k*q + 4*ddd*k*r - 4*ddd*m*v + 2*ddd*m*w + 2*ddd*m*y + 4*ddd*n*v - 2*ddd*n*w - 2*ddd*n*y + 2*ddd*q*u + 2*ddd*q*x - 2*ddd*r*u - 2*ddd*r*x + 2*d**2*f*k*p + 4*d**2*f*k*s + 4*d**2*f*k*z - 2*d**2*f*p*x - 2*d**2*f*s*u - 2*d**2*f*s*x - 2*d**2*f*u*z - 2*d**2*f*x*z + 2*d**2*g*p*v - 2*d**2*g*p*w + 4*d**2*g*s*v - 2*d**2*g*s*w - 2*d**2*g*s*y + 4*d**2*g*v*z - 2*d**2*g*w*z - 2*d**2*g*y*z - 4*d**2*h*p*v + 4*d**2*h*p*w - 8*d**2*h*s*v + 4*d**2*h*s*w + 4*d**2*h*s*y - 8*d**2*h*v*z + 4*d**2*h*w*z + 4*d**2*h*y*z - 4*d**2*k*p*q + 2*d**2*k*p*r - 8*d**2*k*q*s - 8*d**2*k*q*z + 4*d**2*k*r*s + 4*d**2*k*r*z + 2*d**2*l*p*v - 2*d**2*l*p*w + 4*d**2*l*s*v - 2*d**2*l*s*w - 2*d**2*l*s*y + 4*d**2*l*v*z - 2*d**2*l*w*z - 2*d**2*l*y*z - 2*d**2*m*p*v + 2*d**2*m*p*w - 4*d**2*m*s*v + 2*d**2*m*s*w + 2*d**2*m*s*y - 4*d**2*m*v*z + 2*d**2*m*w*z + 2*d**2*m*y*z + 4*d**2*n*p*v - 4*d**2*n*p*w + 8*d**2*n*s*v - 4*d**2*n*s*w - 4*d**2*n*s*y + 8*d**2*n*v*z - 4*d**2*n*w*z - 4*d**2*n*y*z - 2*d**2*o*p*v + 2*d**2*o*p*w - 4*d**2*o*s*v + 2*d**2*o*s*w + 2*d**2*o*s*y - 4*d**2*o*v*z + 2*d**2*o*w*z + 2*d**2*o*y*z + 4*d**2*p*q*x - 2*d**2*p*r*x + 4*d**2*q*s*u + 4*d**2*q*s*x + 4*d**2*q*u*z + 4*d**2*q*x*z - 2*d**2*r*s*u - 2*d**2*r*s*x - 2*d**2*r*u*z - 2*d**2*r*x*z + 2*d*f*g*p**2 - 2*d*f*h*p**2 - 6*d*g*p**2*q + 4*d*g*p**2*r + 8*d*h*p**2*q - 6*d*h*p**2*r - 2*d*l*p**2*q + 2*d*l*p**2*r + 4*f*g*p**2*s - 8*f*h*p**2*s + 4*f*l*p**2*s - 8*g*p**2*q*s + 4*g*p**2*r*s + 16*h*p**2*q*s - 8*h*p**2*r*s - 8*l*p**2*q*s + 4*l*p**2*r*s ) / (dddd*p**2)
    a4 = (2*a*d**2*k - a*d**2*u - a*d**2*x + a*m*p**2 - 2*a*n*p**2 + a*o*p**2 - 4*b*d**2*k + 2*b*d**2*u + 2*b*d**2*x - 2*b*m*p**2 + 4*b*n*p**2 - 2*b*o*p**2 + 2*c*d**2*k - c*d**2*u - c*d**2*x + c*m*p**2 - 2*c*n*p**2 + c*o*p**2 - 2*d**2*f*k + d**2*f*u + d**2*f*x - 2*d**2*g*v + d**2*g*w + d**2*g*y + 4*d**2*h*v - 2*d**2*h*w - 2*d**2*h*y + 4*d**2*k*q - 2*d**2*k*r - 2*d**2*l*v + d**2*l*w + d**2*l*y + 2*d**2*m*v - d**2*m*w - d**2*m*y - 4*d**2*n*v + 2*d**2*n*w + 2*d**2*n*y + 2*d**2*o*v - d**2*o*w - d**2*o*y - 2*d**2*q*u - 2*d**2*q*x + d**2*r*u + d**2*r*x - f*g*p**2 + 2*f*h*p**2 - f*l*p**2 + 2*g*p**2*q - g*p**2*r - 4*h*p**2*q + 2*h*p**2*r + 2*l*p**2*q - l*p**2*r ) / (dddd*p**2)
    """

    d2 = d*d
    d3 = d2*d
    d4 = d3*d
    p2 = p*p
    z2 = z*z
    s2 = s*s
    s3 = s2*s
    s4 = s3*s

    a0 = (2*a*d4*k*p*z + 2*a*d4*k*z2 + a*d4*m*p2 - a*d4*p2*x - 2*a*d4*p*x*z - a*d4*u*z2 - a*d4*x*z2 + 4*a*d3*k*p*s*z + 4*a*d3*k*s*z2 + 4*a*d3*m*p2*s - 2*a*d3*n*p2*s - 2*a*d3*p2*s*x - 4*a*d3*p*s*x*z - 2*a*d3*s*u*z2 - 2*a*d3*s*x*z2 + 2*a*d2*k*p*s2*z + 2*a*d2*k*s2*z2 + 6*a*d2*m*p2*s2 - 6*a*d2*n*p2*s2 + a*d2*o*p2*s2 - a*d2*p2*s2*x - 2*a*d2*p*s2*x*z - a*d2*s2*u*z2 - a*d2*s2*x*z2 + 4*a*d*m*p2*s3 - 6*a*d*n*p2*s3 + 2*a*d*o*p2*s3 + a*m*p2*s4 - 2*a*n*p2*s4 + a*o*p2*s4 - 4*b*d3*k*p*s*z - 4*b*d3*k*s*z2 - 2*b*d3*m*p2*s + 2*b*d3*p2*s*x + 4*b*d3*p*s*x*z + 2*b*d3*s*u*z2 + 2*b*d3*s*x*z2 - 4*b*d2*k*p*s2*z - 4*b*d2*k*s2*z2 - 6*b*d2*m*p2*s2 + 4*b*d2*n*p2*s2 + 2*b*d2*p2*s2*x + 4*b*d2*p*s2*x*z + 2*b*d2*s2*u*z2 + 2*b*d2*s2*x*z2 - 6*b*d*m*p2*s3 + 8*b*d*n*p2*s3 - 2*b*d*o*p2*s3 - 2*b*m*p2*s4 + 4*b*n*p2*s4 - 2*b*o*p2*s4 + 2*c*d2*k*p*s2*z + 2*c*d2*k*s2*z2 + c*d2*m*p2*s2 - c*d2*p2*s2*x - 2*c*d2*p*s2*x*z - c*d2*s2*u*z2 - c*d2*s2*x*z2 + 2*c*d*m*p2*s3 - 2*c*d*n*p2*s3 + c*m*p2*s4 - 2*c*n*p2*s4 + c*o*p2*s4 - d4*g*p2*r + d4*g*p2*w - 2*d4*g*p*v*z + 2*d4*g*p*w*z - 2*d4*g*v*z2 + d4*g*w*z2 + d4*g*y*z2 - 2*d4*k*p*r*z - 2*d4*k*r*z2 - d4*m*p2*w + 2*d4*m*p*v*z - 2*d4*m*p*w*z + 2*d4*m*v*z2 - d4*m*w*z2 - d4*m*y*z2 + d4*p2*r*x + 2*d4*p*r*x*z + d4*r*u*z2 + d4*r*x*z2 + 2*d3*g*p2*q*s - 4*d3*g*p2*r*s + 2*d3*g*p2*s*w - 4*d3*g*p*s*v*z + 4*d3*g*p*s*w*z - 4*d3*g*s*v*z2 + 2*d3*g*s*w*z2 + 2*d3*g*s*y*z2 + 2*d3*h*p2*r*s - 2*d3*h*p2*s*w + 4*d3*h*p*s*v*z - 4*d3*h*p*s*w*z + 4*d3*h*s*v*z2 - 2*d3*h*s*w*z2 - 2*d3*h*s*y*z2 + 4*d3*k*p*q*s*z - 4*d3*k*p*r*s*z + 4*d3*k*q*s*z2 - 4*d3*k*r*s*z2 - 2*d3*m*p2*s*w + 4*d3*m*p*s*v*z - 4*d3*m*p*s*w*z + 4*d3*m*s*v*z2 - 2*d3*m*s*w*z2 - 2*d3*m*s*y*z2 + 2*d3*n*p2*s*w - 4*d3*n*p*s*v*z + 4*d3*n*p*s*w*z - 4*d3*n*s*v*z2 + 2*d3*n*s*w*z2 + 2*d3*n*s*y*z2 - 2*d3*p2*q*s*x + 2*d3*p2*r*s*x - 4*d3*p*q*s*x*z + 4*d3*p*r*s*x*z - 2*d3*q*s*u*z2 - 2*d3*q*s*x*z2 + 2*d3*r*s*u*z2 + 2*d3*r*s*x*z2 - d2*f*g*p2*s2 - 2*d2*f*k*p*s2*z - 2*d2*f*k*s2*z2 + d2*f*p2*s2*x + 2*d2*f*p*s2*x*z + d2*f*s2*u*z2 + d2*f*s2*x*z2 + 6*d2*g*p2*q*s2 - 6*d2*g*p2*r*s2 + d2*g*p2*s2*w - 2*d2*g*p*s2*v*z + 2*d2*g*p*s2*w*z - 2*d2*g*s2*v*z2 + d2*g*s2*w*z2 + d2*g*s2*y*z2 - 4*d2*h*p2*q*s2 + 6*d2*h*p2*r*s2 - 2*d2*h*p2*s2*w + 4*d2*h*p*s2*v*z - 4*d2*h*p*s2*w*z + 4*d2*h*s2*v*z2 - 2*d2*h*s2*w*z2 - 2*d2*h*s2*y*z2 + 4*d2*k*p*q*s2*z - 2*d2*k*p*r*s2*z + 4*d2*k*q*s2*z2 - 2*d2*k*r*s2*z2 - d2*l*p2*r*s2 + d2*l*p2*s2*w - 2*d2*l*p*s2*v*z + 2*d2*l*p*s2*w*z - 2*d2*l*s2*v*z2 + d2*l*s2*w*z2 + d2*l*s2*y*z2 - d2*m*p2*s2*w + 2*d2*m*p*s2*v*z - 2*d2*m*p*s2*w*z + 2*d2*m*s2*v*z2 - d2*m*s2*w*z2 - d2*m*s2*y*z2 + 2*d2*n*p2*s2*w - 4*d2*n*p*s2*v*z + 4*d2*n*p*s2*w*z - 4*d2*n*s2*v*z2 + 2*d2*n*s2*w*z2 + 2*d2*n*s2*y*z2 - d2*o*p2*s2*w + 2*d2*o*p*s2*v*z - 2*d2*o*p*s2*w*z + 2*d2*o*s2*v*z2 - d2*o*s2*w*z2 - d2*o*s2*y*z2 - 2*d2*p2*q*s2*x + d2*p2*r*s2*x - 4*d2*p*q*s2*x*z + 2*d2*p*r*s2*x*z - 2*d2*q*s2*u*z2 - 2*d2*q*s2*x*z2 + d2*r*s2*u*z2 + d2*r*s2*x*z2 - 2*d*f*g*p2*s3 + 2*d*f*h*p2*s3 + 6*d*g*p2*q*s3 - 4*d*g*p2*r*s3 - 8*d*h*p2*q*s3 + 6*d*h*p2*r*s3 + 2*d*l*p2*q*s3 - 2*d*l*p2*r*s3 - f*g*p2*s4 + 2*f*h*p2*s4 - f*l*p2*s4 + 2*g*p2*q*s4 - g*p2*r*s4 - 4*h*p2*q*s4 + 2*h*p2*r*s4 + 2*l*p2*q*s4 - l*p2*r*s4 ) / (d4*p2)
    a1 = (-2*a*d4*k*p - 4*a*d4*k*z + 2*a*d4*p*x + 2*a*d4*u*z + 2*a*d4*x*z - 4*a*d3*k*p*s - 4*a*d3*k*p*z - 8*a*d3*k*s*z - 4*a*d3*k*z2 - 4*a*d3*m*p2 + 2*a*d3*n*p2 + 2*a*d3*p2*x + 4*a*d3*p*s*x + 4*a*d3*p*x*z + 4*a*d3*s*u*z + 4*a*d3*s*x*z + 2*a*d3*u*z2 + 2*a*d3*x*z2 - 2*a*d2*k*p*s2 - 4*a*d2*k*p*s*z - 4*a*d2*k*s2*z - 4*a*d2*k*s*z2 - 12*a*d2*m*p2*s + 12*a*d2*n*p2*s - 2*a*d2*o*p2*s + 2*a*d2*p2*s*x + 2*a*d2*p*s2*x + 4*a*d2*p*s*x*z + 2*a*d2*s2*u*z + 2*a*d2*s2*x*z + 2*a*d2*s*u*z2 + 2*a*d2*s*x*z2 - 12*a*d*m*p2*s2 + 18*a*d*n*p2*s2 - 6*a*d*o*p2*s2 - 4*a*m*p2*s3 + 8*a*n*p2*s3 - 4*a*o*p2*s3 + 4*b*d3*k*p*s + 4*b*d3*k*p*z + 8*b*d3*k*s*z + 4*b*d3*k*z2 + 2*b*d3*m*p2 - 2*b*d3*p2*x - 4*b*d3*p*s*x - 4*b*d3*p*x*z - 4*b*d3*s*u*z - 4*b*d3*s*x*z - 2*b*d3*u*z2 - 2*b*d3*x*z2 + 4*b*d2*k*p*s2 + 8*b*d2*k*p*s*z + 8*b*d2*k*s2*z + 8*b*d2*k*s*z2 + 12*b*d2*m*p2*s - 8*b*d2*n*p2*s - 4*b*d2*p2*s*x - 4*b*d2*p*s2*x - 8*b*d2*p*s*x*z - 4*b*d2*s2*u*z - 4*b*d2*s2*x*z - 4*b*d2*s*u*z2 - 4*b*d2*s*x*z2 + 18*b*d*m*p2*s2 - 24*b*d*n*p2*s2 + 6*b*d*o*p2*s2 + 8*b*m*p2*s3 - 16*b*n*p2*s3 + 8*b*o*p2*s3 - 2*c*d2*k*p*s2 - 4*c*d2*k*p*s*z - 4*c*d2*k*s2*z - 4*c*d2*k*s*z2 - 2*c*d2*m*p2*s + 2*c*d2*p2*s*x + 2*c*d2*p*s2*x + 4*c*d2*p*s*x*z + 2*c*d2*s2*u*z + 2*c*d2*s2*x*z + 2*c*d2*s*u*z2 + 2*c*d2*s*x*z2 - 6*c*d*m*p2*s2 + 6*c*d*n*p2*s2 - 4*c*m*p2*s3 + 8*c*n*p2*s3 - 4*c*o*p2*s3 + 2*d4*g*p*v - 2*d4*g*p*w + 4*d4*g*v*z - 2*d4*g*w*z - 2*d4*g*y*z + 2*d4*k*p*r + 4*d4*k*r*z - 2*d4*m*p*v + 2*d4*m*p*w - 4*d4*m*v*z + 2*d4*m*w*z + 2*d4*m*y*z - 2*d4*p*r*x - 2*d4*r*u*z - 2*d4*r*x*z - 2*d3*g*p2*q + 4*d3*g*p2*r - 2*d3*g*p2*w + 4*d3*g*p*s*v - 4*d3*g*p*s*w + 4*d3*g*p*v*z - 4*d3*g*p*w*z + 8*d3*g*s*v*z - 4*d3*g*s*w*z - 4*d3*g*s*y*z + 4*d3*g*v*z2 - 2*d3*g*w*z2 - 2*d3*g*y*z2 - 2*d3*h*p2*r + 2*d3*h*p2*w - 4*d3*h*p*s*v + 4*d3*h*p*s*w - 4*d3*h*p*v*z + 4*d3*h*p*w*z - 8*d3*h*s*v*z + 4*d3*h*s*w*z + 4*d3*h*s*y*z - 4*d3*h*v*z2 + 2*d3*h*w*z2 + 2*d3*h*y*z2 - 4*d3*k*p*q*s - 4*d3*k*p*q*z + 4*d3*k*p*r*s + 4*d3*k*p*r*z - 8*d3*k*q*s*z - 4*d3*k*q*z2 + 8*d3*k*r*s*z + 4*d3*k*r*z2 + 2*d3*m*p2*w - 4*d3*m*p*s*v + 4*d3*m*p*s*w - 4*d3*m*p*v*z + 4*d3*m*p*w*z - 8*d3*m*s*v*z + 4*d3*m*s*w*z + 4*d3*m*s*y*z - 4*d3*m*v*z2 + 2*d3*m*w*z2 + 2*d3*m*y*z2 - 2*d3*n*p2*w + 4*d3*n*p*s*v - 4*d3*n*p*s*w + 4*d3*n*p*v*z - 4*d3*n*p*w*z + 8*d3*n*s*v*z - 4*d3*n*s*w*z - 4*d3*n*s*y*z + 4*d3*n*v*z2 - 2*d3*n*w*z2 - 2*d3*n*y*z2 + 2*d3*p2*q*x - 2*d3*p2*r*x + 4*d3*p*q*s*x + 4*d3*p*q*x*z - 4*d3*p*r*s*x - 4*d3*p*r*x*z + 4*d3*q*s*u*z + 4*d3*q*s*x*z + 2*d3*q*u*z2 + 2*d3*q*x*z2 - 4*d3*r*s*u*z - 4*d3*r*s*x*z - 2*d3*r*u*z2 - 2*d3*r*x*z2 + 2*d2*f*g*p2*s + 2*d2*f*k*p*s2 + 4*d2*f*k*p*s*z + 4*d2*f*k*s2*z + 4*d2*f*k*s*z2 - 2*d2*f*p2*s*x - 2*d2*f*p*s2*x - 4*d2*f*p*s*x*z - 2*d2*f*s2*u*z - 2*d2*f*s2*x*z - 2*d2*f*s*u*z2 - 2*d2*f*s*x*z2 - 12*d2*g*p2*q*s + 12*d2*g*p2*r*s - 2*d2*g*p2*s*w + 2*d2*g*p*s2*v - 2*d2*g*p*s2*w + 4*d2*g*p*s*v*z - 4*d2*g*p*s*w*z + 4*d2*g*s2*v*z - 2*d2*g*s2*w*z - 2*d2*g*s2*y*z + 4*d2*g*s*v*z2 - 2*d2*g*s*w*z2 - 2*d2*g*s*y*z2 + 8*d2*h*p2*q*s - 12*d2*h*p2*r*s + 4*d2*h*p2*s*w - 4*d2*h*p*s2*v + 4*d2*h*p*s2*w - 8*d2*h*p*s*v*z + 8*d2*h*p*s*w*z - 8*d2*h*s2*v*z + 4*d2*h*s2*w*z + 4*d2*h*s2*y*z - 8*d2*h*s*v*z2 + 4*d2*h*s*w*z2 + 4*d2*h*s*y*z2 - 4*d2*k*p*q*s2 - 8*d2*k*p*q*s*z + 2*d2*k*p*r*s2 + 4*d2*k*p*r*s*z - 8*d2*k*q*s2*z - 8*d2*k*q*s*z2 + 4*d2*k*r*s2*z + 4*d2*k*r*s*z2 + 2*d2*l*p2*r*s - 2*d2*l*p2*s*w + 2*d2*l*p*s2*v - 2*d2*l*p*s2*w + 4*d2*l*p*s*v*z - 4*d2*l*p*s*w*z + 4*d2*l*s2*v*z - 2*d2*l*s2*w*z - 2*d2*l*s2*y*z + 4*d2*l*s*v*z2 - 2*d2*l*s*w*z2 - 2*d2*l*s*y*z2 + 2*d2*m*p2*s*w - 2*d2*m*p*s2*v + 2*d2*m*p*s2*w - 4*d2*m*p*s*v*z + 4*d2*m*p*s*w*z - 4*d2*m*s2*v*z + 2*d2*m*s2*w*z + 2*d2*m*s2*y*z - 4*d2*m*s*v*z2 + 2*d2*m*s*w*z2 + 2*d2*m*s*y*z2 - 4*d2*n*p2*s*w + 4*d2*n*p*s2*v - 4*d2*n*p*s2*w + 8*d2*n*p*s*v*z - 8*d2*n*p*s*w*z + 8*d2*n*s2*v*z - 4*d2*n*s2*w*z - 4*d2*n*s2*y*z + 8*d2*n*s*v*z2 - 4*d2*n*s*w*z2 - 4*d2*n*s*y*z2 + 2*d2*o*p2*s*w - 2*d2*o*p*s2*v + 2*d2*o*p*s2*w - 4*d2*o*p*s*v*z + 4*d2*o*p*s*w*z - 4*d2*o*s2*v*z + 2*d2*o*s2*w*z + 2*d2*o*s2*y*z - 4*d2*o*s*v*z2 + 2*d2*o*s*w*z2 + 2*d2*o*s*y*z2 + 4*d2*p2*q*s*x - 2*d2*p2*r*s*x + 4*d2*p*q*s2*x + 8*d2*p*q*s*x*z - 2*d2*p*r*s2*x - 4*d2*p*r*s*x*z + 4*d2*q*s2*u*z + 4*d2*q*s2*x*z + 4*d2*q*s*u*z2 + 4*d2*q*s*x*z2 - 2*d2*r*s2*u*z - 2*d2*r*s2*x*z - 2*d2*r*s*u*z2 - 2*d2*r*s*x*z2 + 6*d*f*g*p2*s2 - 6*d*f*h*p2*s2 - 18*d*g*p2*q*s2 + 12*d*g*p2*r*s2 + 24*d*h*p2*q*s2 - 18*d*h*p2*r*s2 - 6*d*l*p2*q*s2 + 6*d*l*p2*r*s2 + 4*f*g*p2*s3 - 8*f*h*p2*s3 + 4*f*l*p2*s3 - 8*g*p2*q*s3 + 4*g*p2*r*s3 + 16*h*p2*q*s3 - 8*h*p2*r*s3 - 8*l*p2*q*s3 + 4*l*p2*r*s3 ) / (d4*p2)
    a2 = (2*a*d4*k - a*d4*u - a*d4*x + 4*a*d3*k*p + 4*a*d3*k*s + 8*a*d3*k*z - 4*a*d3*p*x - 2*a*d3*s*u - 2*a*d3*s*x - 4*a*d3*u*z - 4*a*d3*x*z + 4*a*d2*k*p*s + 2*a*d2*k*p*z + 2*a*d2*k*s2 + 8*a*d2*k*s*z + 2*a*d2*k*z2 + 6*a*d2*m*p2 - 6*a*d2*n*p2 + a*d2*o*p2 - a*d2*p2*x - 4*a*d2*p*s*x - 2*a*d2*p*x*z - a*d2*s2*u - a*d2*s2*x - 4*a*d2*s*u*z - 4*a*d2*s*x*z - a*d2*u*z2 - a*d2*x*z2 + 12*a*d*m*p2*s - 18*a*d*n*p2*s + 6*a*d*o*p2*s + 6*a*m*p2*s2 - 12*a*n*p2*s2 + 6*a*o*p2*s2 - 4*b*d3*k*p - 4*b*d3*k*s - 8*b*d3*k*z + 4*b*d3*p*x + 2*b*d3*s*u + 2*b*d3*s*x + 4*b*d3*u*z + 4*b*d3*x*z - 8*b*d2*k*p*s - 4*b*d2*k*p*z - 4*b*d2*k*s2 - 16*b*d2*k*s*z - 4*b*d2*k*z2 - 6*b*d2*m*p2 + 4*b*d2*n*p2 + 2*b*d2*p2*x + 8*b*d2*p*s*x + 4*b*d2*p*x*z + 2*b*d2*s2*u + 2*b*d2*s2*x + 8*b*d2*s*u*z + 8*b*d2*s*x*z + 2*b*d2*u*z2 + 2*b*d2*x*z2 - 18*b*d*m*p2*s + 24*b*d*n*p2*s - 6*b*d*o*p2*s - 12*b*m*p2*s2 + 24*b*n*p2*s2 - 12*b*o*p2*s2 + 4*c*d2*k*p*s + 2*c*d2*k*p*z + 2*c*d2*k*s2 + 8*c*d2*k*s*z + 2*c*d2*k*z2 + c*d2*m*p2 - c*d2*p2*x - 4*c*d2*p*s*x - 2*c*d2*p*x*z - c*d2*s2*u - c*d2*s2*x - 4*c*d2*s*u*z - 4*c*d2*s*x*z - c*d2*u*z2 - c*d2*x*z2 + 6*c*d*m*p2*s - 6*c*d*n*p2*s + 6*c*m*p2*s2 - 12*c*n*p2*s2 + 6*c*o*p2*s2 - 2*d4*g*v + d4*g*w + d4*g*y - 2*d4*k*r + 2*d4*m*v - d4*m*w - d4*m*y + d4*r*u + d4*r*x - 4*d3*g*p*v + 4*d3*g*p*w - 4*d3*g*s*v + 2*d3*g*s*w + 2*d3*g*s*y - 8*d3*g*v*z + 4*d3*g*w*z + 4*d3*g*y*z + 4*d3*h*p*v - 4*d3*h*p*w + 4*d3*h*s*v - 2*d3*h*s*w - 2*d3*h*s*y + 8*d3*h*v*z - 4*d3*h*w*z - 4*d3*h*y*z + 4*d3*k*p*q - 4*d3*k*p*r + 4*d3*k*q*s + 8*d3*k*q*z - 4*d3*k*r*s - 8*d3*k*r*z + 4*d3*m*p*v - 4*d3*m*p*w + 4*d3*m*s*v - 2*d3*m*s*w - 2*d3*m*s*y + 8*d3*m*v*z - 4*d3*m*w*z - 4*d3*m*y*z - 4*d3*n*p*v + 4*d3*n*p*w - 4*d3*n*s*v + 2*d3*n*s*w + 2*d3*n*s*y - 8*d3*n*v*z + 4*d3*n*w*z + 4*d3*n*y*z - 4*d3*p*q*x + 4*d3*p*r*x - 2*d3*q*s*u - 2*d3*q*s*x - 4*d3*q*u*z - 4*d3*q*x*z + 2*d3*r*s*u + 2*d3*r*s*x + 4*d3*r*u*z + 4*d3*r*x*z - d2*f*g*p2 - 4*d2*f*k*p*s - 2*d2*f*k*p*z - 2*d2*f*k*s2 - 8*d2*f*k*s*z - 2*d2*f*k*z2 + d2*f*p2*x + 4*d2*f*p*s*x + 2*d2*f*p*x*z + d2*f*s2*u + d2*f*s2*x + 4*d2*f*s*u*z + 4*d2*f*s*x*z + d2*f*u*z2 + d2*f*x*z2 + 6*d2*g*p2*q - 6*d2*g*p2*r + d2*g*p2*w - 4*d2*g*p*s*v + 4*d2*g*p*s*w - 2*d2*g*p*v*z + 2*d2*g*p*w*z - 2*d2*g*s2*v + d2*g*s2*w + d2*g*s2*y - 8*d2*g*s*v*z + 4*d2*g*s*w*z + 4*d2*g*s*y*z - 2*d2*g*v*z2 + d2*g*w*z2 + d2*g*y*z2 - 4*d2*h*p2*q + 6*d2*h*p2*r - 2*d2*h*p2*w + 8*d2*h*p*s*v - 8*d2*h*p*s*w + 4*d2*h*p*v*z - 4*d2*h*p*w*z + 4*d2*h*s2*v - 2*d2*h*s2*w - 2*d2*h*s2*y + 16*d2*h*s*v*z - 8*d2*h*s*w*z - 8*d2*h*s*y*z + 4*d2*h*v*z2 - 2*d2*h*w*z2 - 2*d2*h*y*z2 + 8*d2*k*p*q*s + 4*d2*k*p*q*z - 4*d2*k*p*r*s - 2*d2*k*p*r*z + 4*d2*k*q*s2 + 16*d2*k*q*s*z + 4*d2*k*q*z2 - 2*d2*k*r*s2 - 8*d2*k*r*s*z - 2*d2*k*r*z2 - d2*l*p2*r + d2*l*p2*w - 4*d2*l*p*s*v + 4*d2*l*p*s*w - 2*d2*l*p*v*z + 2*d2*l*p*w*z - 2*d2*l*s2*v + d2*l*s2*w + d2*l*s2*y - 8*d2*l*s*v*z + 4*d2*l*s*w*z + 4*d2*l*s*y*z - 2*d2*l*v*z2 + d2*l*w*z2 + d2*l*y*z2 - d2*m*p2*w + 4*d2*m*p*s*v - 4*d2*m*p*s*w + 2*d2*m*p*v*z - 2*d2*m*p*w*z + 2*d2*m*s2*v - d2*m*s2*w - d2*m*s2*y + 8*d2*m*s*v*z - 4*d2*m*s*w*z - 4*d2*m*s*y*z + 2*d2*m*v*z2 - d2*m*w*z2 - d2*m*y*z2 + 2*d2*n*p2*w - 8*d2*n*p*s*v + 8*d2*n*p*s*w - 4*d2*n*p*v*z + 4*d2*n*p*w*z - 4*d2*n*s2*v + 2*d2*n*s2*w + 2*d2*n*s2*y - 16*d2*n*s*v*z + 8*d2*n*s*w*z + 8*d2*n*s*y*z - 4*d2*n*v*z2 + 2*d2*n*w*z2 + 2*d2*n*y*z2 - d2*o*p2*w + 4*d2*o*p*s*v - 4*d2*o*p*s*w + 2*d2*o*p*v*z - 2*d2*o*p*w*z + 2*d2*o*s2*v - d2*o*s2*w - d2*o*s2*y + 8*d2*o*s*v*z - 4*d2*o*s*w*z - 4*d2*o*s*y*z + 2*d2*o*v*z2 - d2*o*w*z2 - d2*o*y*z2 - 2*d2*p2*q*x + d2*p2*r*x - 8*d2*p*q*s*x - 4*d2*p*q*x*z + 4*d2*p*r*s*x + 2*d2*p*r*x*z - 2*d2*q*s2*u - 2*d2*q*s2*x - 8*d2*q*s*u*z - 8*d2*q*s*x*z - 2*d2*q*u*z2 - 2*d2*q*x*z2 + d2*r*s2*u + d2*r*s2*x + 4*d2*r*s*u*z + 4*d2*r*s*x*z + d2*r*u*z2 + d2*r*x*z2 - 6*d*f*g*p2*s + 6*d*f*h*p2*s + 18*d*g*p2*q*s - 12*d*g*p2*r*s - 24*d*h*p2*q*s + 18*d*h*p2*r*s + 6*d*l*p2*q*s - 6*d*l*p2*r*s - 6*f*g*p2*s2 + 12*f*h*p2*s2 - 6*f*l*p2*s2 + 12*g*p2*q*s2 - 6*g*p2*r*s2 - 24*h*p2*q*s2 + 12*h*p2*r*s2 + 12*l*p2*q*s2 - 6*l*p2*r*s2 ) / (d4*p2)
    a3 = (-4*a*d3*k + 2*a*d3*u + 2*a*d3*x - 2*a*d2*k*p - 4*a*d2*k*s - 4*a*d2*k*z + 2*a*d2*p*x + 2*a*d2*s*u + 2*a*d2*s*x + 2*a*d2*u*z + 2*a*d2*x*z - 4*a*d*m*p2 + 6*a*d*n*p2 - 2*a*d*o*p2 - 4*a*m*p2*s + 8*a*n*p2*s - 4*a*o*p2*s + 4*b*d3*k - 2*b*d3*u - 2*b*d3*x + 4*b*d2*k*p + 8*b*d2*k*s + 8*b*d2*k*z - 4*b*d2*p*x - 4*b*d2*s*u - 4*b*d2*s*x - 4*b*d2*u*z - 4*b*d2*x*z + 6*b*d*m*p2 - 8*b*d*n*p2 + 2*b*d*o*p2 + 8*b*m*p2*s - 16*b*n*p2*s + 8*b*o*p2*s - 2*c*d2*k*p - 4*c*d2*k*s - 4*c*d2*k*z + 2*c*d2*p*x + 2*c*d2*s*u + 2*c*d2*s*x + 2*c*d2*u*z + 2*c*d2*x*z - 2*c*d*m*p2 + 2*c*d*n*p2 - 4*c*m*p2*s + 8*c*n*p2*s - 4*c*o*p2*s + 4*d3*g*v - 2*d3*g*w - 2*d3*g*y - 4*d3*h*v + 2*d3*h*w + 2*d3*h*y - 4*d3*k*q + 4*d3*k*r - 4*d3*m*v + 2*d3*m*w + 2*d3*m*y + 4*d3*n*v - 2*d3*n*w - 2*d3*n*y + 2*d3*q*u + 2*d3*q*x - 2*d3*r*u - 2*d3*r*x + 2*d2*f*k*p + 4*d2*f*k*s + 4*d2*f*k*z - 2*d2*f*p*x - 2*d2*f*s*u - 2*d2*f*s*x - 2*d2*f*u*z - 2*d2*f*x*z + 2*d2*g*p*v - 2*d2*g*p*w + 4*d2*g*s*v - 2*d2*g*s*w - 2*d2*g*s*y + 4*d2*g*v*z - 2*d2*g*w*z - 2*d2*g*y*z - 4*d2*h*p*v + 4*d2*h*p*w - 8*d2*h*s*v + 4*d2*h*s*w + 4*d2*h*s*y - 8*d2*h*v*z + 4*d2*h*w*z + 4*d2*h*y*z - 4*d2*k*p*q + 2*d2*k*p*r - 8*d2*k*q*s - 8*d2*k*q*z + 4*d2*k*r*s + 4*d2*k*r*z + 2*d2*l*p*v - 2*d2*l*p*w + 4*d2*l*s*v - 2*d2*l*s*w - 2*d2*l*s*y + 4*d2*l*v*z - 2*d2*l*w*z - 2*d2*l*y*z - 2*d2*m*p*v + 2*d2*m*p*w - 4*d2*m*s*v + 2*d2*m*s*w + 2*d2*m*s*y - 4*d2*m*v*z + 2*d2*m*w*z + 2*d2*m*y*z + 4*d2*n*p*v - 4*d2*n*p*w + 8*d2*n*s*v - 4*d2*n*s*w - 4*d2*n*s*y + 8*d2*n*v*z - 4*d2*n*w*z - 4*d2*n*y*z - 2*d2*o*p*v + 2*d2*o*p*w - 4*d2*o*s*v + 2*d2*o*s*w + 2*d2*o*s*y - 4*d2*o*v*z + 2*d2*o*w*z + 2*d2*o*y*z + 4*d2*p*q*x - 2*d2*p*r*x + 4*d2*q*s*u + 4*d2*q*s*x + 4*d2*q*u*z + 4*d2*q*x*z - 2*d2*r*s*u - 2*d2*r*s*x - 2*d2*r*u*z - 2*d2*r*x*z + 2*d*f*g*p2 - 2*d*f*h*p2 - 6*d*g*p2*q + 4*d*g*p2*r + 8*d*h*p2*q - 6*d*h*p2*r - 2*d*l*p2*q + 2*d*l*p2*r + 4*f*g*p2*s - 8*f*h*p2*s + 4*f*l*p2*s - 8*g*p2*q*s + 4*g*p2*r*s + 16*h*p2*q*s - 8*h*p2*r*s - 8*l*p2*q*s + 4*l*p2*r*s ) / (d4*p2)
    a4 = (2*a*d2*k - a*d2*u - a*d2*x + a*m*p2 - 2*a*n*p2 + a*o*p2 - 4*b*d2*k + 2*b*d2*u + 2*b*d2*x - 2*b*m*p2 + 4*b*n*p2 - 2*b*o*p2 + 2*c*d2*k - c*d2*u - c*d2*x + c*m*p2 - 2*c*n*p2 + c*o*p2 - 2*d2*f*k + d2*f*u + d2*f*x - 2*d2*g*v + d2*g*w + d2*g*y + 4*d2*h*v - 2*d2*h*w - 2*d2*h*y + 4*d2*k*q - 2*d2*k*r - 2*d2*l*v + d2*l*w + d2*l*y + 2*d2*m*v - d2*m*w - d2*m*y - 4*d2*n*v + 2*d2*n*w + 2*d2*n*y + 2*d2*o*v - d2*o*w - d2*o*y - 2*d2*q*u - 2*d2*q*x + d2*r*u + d2*r*x - f*g*p2 + 2*f*h*p2 - f*l*p2 + 2*g*p2*q - g*p2*r - 4*h*p2*q + 2*h*p2*r + 2*l*p2*q - l*p2*r ) / (d4*p2)

    coeff = [a4, a3, a2, a1, a0]

    r = np.roots(coeff)

    N = len(r)
    K = 0

    rroots = []

    while K < N:
        v = r[K]

        if im(v) == 0:
            v = re(v)
            if v >= it.x - eps and v <= it.x + eps:
                rroots += [it.x]
            elif v >= it.y - eps and v <= it.y + eps:
                rroots += [it.y]
            elif v >= it.x and v <= it.y:
                rroots += [v]

        K += 1

    rroots.sort()

    e_exec_time = time.time()
    _exec_time = e_exec_time - s_exec_time

    return _exec_time, rroots

#-------------------------------------------------------------------
# Function for working with segments
#-------------------------------------------------------------------

def on_segment_with_eps(px, py, qx, qy, rx, ry, epsilon):
    if min(px, qx) - epsilon <= rx <= max(px, qx) + epsilon and min(py, qy) - epsilon <= ry <= max(py, qy) + epsilon:
        return True

    return False

def on_segment_with_eps2(minx, miny, maxx, maxy, rx, ry, epsilon):

    if minx > maxx:
        if rx < maxx - epsilon or rx > minx + epsilon:
            return False
        """
        if rx < maxx - epsilon:
            return False
        if rx > minx + epsilon:
            return False
        """
    else:
        if rx < minx - epsilon or rx > maxx + epsilon:
            return False
        """
        if rx < minx - epsilon:
            return False
        if rx > maxx + epsilon:
            return False
        """

    if miny > maxy:
        if ry < maxy - epsilon or ry > miny + epsilon:
            return False
    else:
        if ry < miny - epsilon or ry > maxy + epsilon:
            return False


    return True

#-------------------------------------------------------------------
# Function tools
#-------------------------------------------------------------------

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

def f_p(x, y, m):
    if m == None:
        b = x
    else:
        b = -(m * x) + y

    return m, b

#-------------------------------------------------------------------
# MR X MP ST Operations
#-------------------------------------------------------------------

def get_mr_mp_intersections(MS, mp, initial_state, final_state, op = 1, n_linear_traj = False, ccw = True):
    global begin_exec_time
    global precision_0

    msegs = []

    for ms in MS:
        msegs += [create_moving_segment([ms], pass_through_control_points)]

    intersections = None

    if n_linear_traj:
        nsegs = len(msegs)
        i = 0
        while i < nsegs:
            intersections = get_intersections_4(msegs[i], mp, interval, i, intersections)
            i += 1
        #for ms in msegs:
        #    intersections = get_intersections_4(ms, mp, interval, intersections)
    else:
        nsegs = len(msegs)
        i = 0
        while i < nsegs:
            intersections = get_intersections_3(msegs[i], mp, interval, i, intersections)
            i += 1
        #for ms in msegs:    
        #    intersections = get_intersections_3(ms, mp, interval, intersections)

    if initial_state == State.Inside or initial_state == State.Touch:
        intersections = [interval.begin()] + intersections

    if final_state == State.Inside or final_state == State.Touch:
        intersections += [interval.end()]

    #a_time = time.time()
    intersections = process_intersections(intersections, mp, msegs, initial_state, final_state, ccw)
    #b_time = time.time()
    #print(b_time - a_time)

    intersection_geom = None

    if op == Operation.Disjoint.value:

        comp = []

        N = len(intersections)

        if N == 0:
            I = Interval(interval.x, interval.y, True, True)
            comp = [I]
        else:
            t0 = intersections[0]

            if isinstance(t0, Interval):
                if t0.x > interval.x:
                    I = Interval(interval.x, t0.x, True, False)
                    comp = [I]
            else:
                if t0 > interval.x:
                    I = Interval(interval.x, t0, True, False)
                    comp = [I]

            J = 1
            
            while J < N:
                t1 = intersections[J-1]
                t2 = intersections[J]

                if isinstance(t1, Interval):
                    t1 = t1.y

                if isinstance(t2, Interval):
                    t2 = t2.x

                I = Interval(t1, t2, False, False)
                comp += [I]

                J += 1

            t0 = intersections[N-1]

            if isinstance(t0, Interval):
                if t0.y < interval.y:
                    I = Interval(t0.y, interval.y, False, True)
                    comp += [I]
            else:
                if t0 < interval.y:
                    I = Interval(t0, interval.y, False, True)
                    comp += [I]

        intersections = comp
    elif op == Operation.Within.value or op == Operation.Contains.value:
        comp = []
        N = len(intersections)

        if N > 0:
            for intersection in intersections:
                if isinstance(intersection, Interval):
                    I = Interval(intersection.x, intersection.y, False, False)
                    comp += [I]

        intersections = comp
    elif op == Operation.Touches.value:
        comp = []
        N = len(intersections)

        if N > 0:
            for intersection in intersections:
                if isinstance(intersection, Interval):
                    comp += [intersection.x, intersection.y]
                else:
                    comp += [intersection]

        intersections = comp

    end_exec_time = time.time()
    exec_time = end_exec_time - begin_exec_time

    day, hour, minutes, seconds = seconds_to_time(int(exec_time))
    #print('{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0))

    get_samples_for_out(msegs, mp, interval, n_samples, intersections)
	
    sday, shour, sminutes, sseconds = seconds_to_time(int(solver_exec_time))

    if print_intersection_information:
        print(get_intersection_information(intersections, msegs, mp, op))

    if print_solver_execution_time:
        print('N: ' + str(len(msegs)) + ', ' + format(exec_time, precision) + ' : ' + format(solver_exec_time, precision) + ', ' + format((solver_exec_time * 100) / exec_time, precision) + '%, TET: ' + '{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0) + ', SET: ' + '{:0>2}'.format(sseconds, precision_0) + ' Sec, NE: ' + str(solver_exec_times))

#-------------------------------------------------------------------
#-------------------------------------------------------------------
"""

	Tests:
	
		python mr_mp_pred3.py 1

	Usage examples:
	
	    disjoint, inside, disjoint
		python mr_mp_pred3.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON ((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "755,489#895,774#1000,2000" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"
		
	    disjoint, inside, disjoint, inside, disjoint
		python mr_mp_pred3.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON ((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "802.826,764.752#990.308,633.951#1000,2000" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"		
		
"""
#-------------------------------------------------------------------

# 1. get input

get_params()

# Tests

if TESTING:
    p_wkt = 'POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))'
    q_wkt = 'POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))'

    tests_r = []
    N = NTESTS

    ccw = True

    tests_r += [tests(N, p_wkt, q_wkt, '755,489#895,774#1000,2000', False, ccw)]

    tests_r += [tests(N, p_wkt, q_wkt, '802.826,764.752#990.308,633.951#1000,2000', False, ccw)]

    tests_r += [tests(N, p_wkt, q_wkt, '802.826,764.752#896.5,690.5#990.308,633.951#1000,2000', True, ccw)]

    p_wkt = 'Polygon ((625.60285412388361692 848.36828579784025806, 596.34076760988864407 823.55912549249683252, 603.97435539614821209 808.9280822354993461, 620.51379559971064737 811.47261149758583088, 631.32804496357823609 804.47515602684779878, 633.23644191014318494 788.5718481388072405, 613.51634012897261528 763.12655551794205167, 610.33567855136459457 720.50569037799289163, 638.3255004343161545 698.24105933473595087, 668.85985157935442658 691.8797361795195684, 691.12448262261136733 700.14945628130078603, 698.12193809334928574 717.32502880038475723, 689.21608567604641848 739.58965984364169799, 702.57486430200071936 756.12910004720413326, 734.3814800780820633 751.04004152303116371, 741.3789355488199817 724.32248427112267564, 765.551963538641985 717.32502880038475723, 782.7275360577259562 724.95861658664432525, 792.90565310607189531 757.40136467824743249, 785.9081976353339769 781.57439266806920841, 766.18809585416352093 791.11637740089372528, 728.0201569228659082 786.02731887672064204, 736.92600934016866177 805.7474206578912117, 768.09649280072835609 826.73978707010485323, 797.99471163024497855 821.65072854593176999, 801.81150552337476256 838.82630106501574119, 759.82677269894725214 845.18762422023212366, 752.82931722820933373 860.45479979275114601, 747.10412638851471456 878.26650462735676683, 731.20081850047404259 886.53622472913798447, 715.29751061243325694 878.90263694287841645, 718.47817219004139133 864.90772600140257964, 735.65374470912536253 837.55403643397255564, 719.11430450556304095 825.467522439061554, 708.30005514169533853 810.20034686654253164, 702.57486430200071936 790.48024508537207566, 672.04051315696244728 794.29703897850185967, 676.4934393656139946 810.20034686654253164, 675.22117473457069536 829.92044864771310131, 655.5010729534001257 850.91281505992685652, 625.60285412388361692 848.36828579784025806))'
    q_wkt = 'Polygon ((706.70553660468544876 678.20429095876056635, 707.01292790704860636 670.55041367985040779, 709.60827545294705487 664.44461890553407102, 714.26057379424082683 658.57928610521935298, 725.00787080502414028 649.68326754334066209, 739.03582089360338614 642.04406131037194427, 766.40832508741391393 633.80762860441359408, 794.68321414780643863 626.1420051436441554, 809.91912333364246024 628.30923061171438349, 824.53011422889949245 642.57192193123285051, 826.05050035276190101 660.68601420567802052, 815.15041278239073108 679.33450087900723702, 796.99764382460853085 685.18765912119067707, 808.02377513813564747 714.89963107817834498, 826.28528942405046109 734.38130536065818887, 844.95501619525600745 733.6663519357948644, 854.99991537960602273 741.57738137626654407, 856.10034301207963381 752.35428782721305652, 847.22899691343786799 767.07282902075394304, 831.69144302242420963 770.35449913528145771, 814.84752853876852896 761.17987575671327249, 789.38872163783935321 740.80079354888562193, 774.17553373008604467 774.12468068018188205, 781.67273712903715932 790.18118888486515061, 791.86835373579151565 806.18745794874712374, 775.74486001003947422 810.08677707062679474, 760.43449296249832514 785.43121944686799907, 748.63271334742307772 779.54904339876839003, 735.93964009607088883 774.38666630690158854, 724.17953067452106097 771.00648497330303144, 709.31313846120156086 769.93359364380921761, 712.40755336321126379 760.72012525501531854, 746.10339166142466638 765.0902275964135697, 758.14172836322461535 758.67699862267045319, 770.82401169186437073 739.09554811953898934, 780.84899931447830568 717.75221492337630025, 771.55419992269139584 692.19183373611872412, 753.84645257248826056 697.12184270876082337, 735.44916160316620335 699.71382117740677131, 717.78387790044052963 693.29434257310731482, 706.70553660468544876 678.20429095876056635))'

    tests_r += [tests(N, p_wkt, q_wkt, '707.709,843.823#725.328,782.787#814.051,777.753#1000,2000', True, ccw)]

    tests_r += [tests(N, p_wkt, q_wkt, '765.599,896.680#720.294,747.549#832.299,607.228#1000,2000', True, ccw)]

    tests_r += [tests(N, p_wkt, q_wkt, '765.599,896.680#766.228,760.134#607.030,683.366#1000,2000', True, ccw)]
    # D
    #tests_r += [tests(N, p_wkt, q_wkt, '765.599,896.680#665.550,820.541#668.066,679.591#1000,2000', True)]
    # D
    #tests_r += [tests(N, p_wkt, q_wkt, '765.599,896.680#665.550,820.541#712.743,635.544#1000,2000', True)]
    # D
    tests_r += [tests(N, p_wkt, q_wkt, '765.599,896.680#672.471,804.810#712.743,635.544#1000,2000', True, ccw)]

    p_wkt = 'POLYGON ((-29.42 212.44, 17.20 287.43, 34.41 298.82, 51.61 221.98, 98.21 203.83, 144.81 92.32, 191.42 194.15, 235.33 216.73, 323.15 142.19, 387.49 134.29, 419.66 300.22, 567.66 307.79, 597.81 182.35, 627.96 164.08, 658.11 199.24, 714.58 311.40, 742.81 232.82, 762.26 327.99, 801.16 330.77, 824.96 257.81, 848.77 256.33, 872.57 331.43, 954.05 177.93, 1013.00 200.81, 1042.47 302.44, 1078.37 361.84, 1150.16 294.82, 1170.23 337.87, 1210.37 230.46, 1253.70 321.73, 1297.03 188.93, 1340.35 325.29, 1466.21 186.59, 1604.85 176.78, 1751.08 301.96, 1795.67 230.26, 1884.86 277.87, 1922.49 240.58, 1997.74 206.38, 2015.86 180.14, 2033.98 263.40, 2052.10 308.77, 2196.98 227.49, 2237.98 312.79, 2319.96 356.17, 2350.31 292.22, 2380.66 249.28, 2411.01 216.29, 2455.40 341.12, 2544.18 287.95, 2593.50 176.83, 2642.82 184.41, 2692.14 276.05, 2718.08 275.26, 2769.96 281.54, 2839.24 244.27, 2873.88 220.17, 2892.42 286.40, 2910.96 310.27, 2929.50 273.09, 2976.02 247.09, 3022.53 198.87, 3069.05 101.41, 3159.36 113.55, 3236.47 113.81, 3278.18 65.26, 3319.89 195.02, 3361.61 219.01, 3449.42 78.44, 3493.33 82.48, 3524.40 135.68, 3555.47 222.40, 3586.55 215.18, 3637.44 170.28, 3662.88 203.31, 3748.62 155.93, 3791.85 182.05, 3878.31 195.15, 3922.87 172.60, 3967.42 86.46, 4011.98 171.47, 4130.14 127.08, 4205.47 143.17, 4243.13 87.17, 4297.62 115.06, 4322.95 223.00, 4373.62 94.19, 4406.30 86.17, 4438.98 82.32, 4471.67 263.36, 4617.87 219.95, 4737.95 189.84, 4785.58 272.02, 4833.21 246.66, 4880.83 295.24, 4937.38 147.37, 4965.65 196.90, 4984.81 123.51, 5023.12 233.56, 5053.17 220.47, 5113.25 277.95, 5160.10 253.55, 5253.80 157.13, 5338.70 97.81, 5359.01 71.52, 5379.33 206.18, 5399.64 81.68, 5451.55 81.97, 5477.51 287.15, 5503.75 241.05, 5529.99 102.33, 5556.23 217.23, 5575.97 124.37, 5615.44 109.91, 5644.63 129.37, 5673.82 169.82, 5703.01 299.95, 5750.25 163.37, 5844.73 296.80, 5972.19 110.44, 6095.99 81.16, 6174.11 104.65, 6213.18 156.80, 6271.86 112.84, 6301.21 209.93, 6392.13 260.84, 6419.06 211.76, 6472.92 256.19, 6516.05 112.62, 6537.61 62.95, 6603.50 208.43, 6620.60 24.48, 6637.70 46.99, 6654.81 181.41, 6698.31 149.20, 6741.81 10.49, 6785.31 41.70, 6803.16 53.00, 6821.00 9.80, 6838.85 157.73, 6872.89 40.43, 6940.98 19.24, 6988.21 71.78, 7035.43 196.87, 7082.65 140.15, 7164.01 22.65, 7204.68 20.68, 7319.05 59.96, 7381.38 176.11, 7412.55 59.94, 7436.78 171.10, 7461.01 138.81, 7485.24 174.23, 7518.77 113.98, 7585.82 201.46, 7612.22 206.16, 7665.02 139.60, 7717.42 93.36, 7753.39 152.03, 7789.36 187.50, 7825.33 192.78, 7863.59 69.12, 7882.72 163.00, 7912.78 114.33, 7942.83 238.98, 7972.89 295.53, 8067.59 137.82, 8114.94 229.80, 8158.60 175.10, 8180.42 208.77, 8229.89 139.87, 8328.82 180.89, 8375.31 271.96, 8468.29 129.79, 8524.39 87.01, 8552.44 168.46, 8586.13 159.49, 8602.98 238.67, 8637.13 80.45, 8671.29 90.91, 8705.44 206.73, 8736.28 187.97, 8767.12 135.85, 8797.97 210.79, 8824.33 137.02, 8850.69 250.41, 8877.06 123.71, 8973.16 248.83, 9020.74 223.73, 9068.32 32.78, 9115.91 147.68, 9218.97 227.69, 9322.12 95.86, 9449.62 64.70, 9489.60 26.82, 9509.59 50.20, 9604.37 231.01, 9631.59 123.33, 9686.04 236.14, 9733.76 183.66, 9781.49 215.66, 9829.22 185.08, 9858.96 203.05, 9888.69 80.47, 9918.42 69.80, 9962.55 189.82, 10050.81 233.34, 10079.34 156.30, 10136.42 127.20, 10214.48 228.09, 10290.94 106.78, 10372.26 178.16, 10437.30 148.34, 10469.81 184.57, 10568.55 214.22, 10617.91 271.13, 10696.45 256.79, 10744.27 164.47, 10792.09 276.44, 10839.91 247.89, 10868.17 265.52, 10924.71 238.31, 11002.24 181.80, 11026.58 152.38, 11075.25 219.15, 11224.63 161.72, 11286.29 217.98, 11329.40 165.79, 11350.95 91.76, 11388.22 164.03, 11462.76 154.01, 11525.77 76.53, 11638.09 287.64, 11733.10 256.60, 11824.50 232.73, 11893.39 200.44, 11927.84 143.76, 11975.98 221.29, 12024.12 259.12, 12072.27 182.69, 12130.15 307.41, 12178.69 260.05, 12275.78 138.24, 12306.89 113.15, 12338.00 225.48, 12369.11 147.07, 12432.17 261.66, 12463.70 201.31, 12481.32 267.17, 12498.93 231.43, 12516.55 159.49, 12615.12 221.71, 12707.53 135.17, 12753.74 230.59, 12874.06 181.60, 12904.15 63.84, 12934.23 35.96, 12964.32 193.16, 13007.82 59.29, 13094.84 97.58, 13143.14 150.78, 13167.29 198.45, 13261.75 66.35, 13356.15 71.81, 13389.06 35.12, 13454.90 122.36, 13482.78 68.19, 13510.67 149.66, 13538.56 121.14, 13562.02 159.88, 13608.94 157.99, 13699.52 111.22, 13744.81 60.19, 13770.06 80.92, 13820.57 132.36, 13878.82 69.91, 13907.94 108.06, 13983.43 172.60, 14018.72 140.43, 14089.30 138.06, 14160.86 130.78, 14206.21 81.85, 14228.89 75.11, 14331.26 166.54, 14408.42 142.49, 14447.00 41.47, 14486.04 99.15, 14564.14 103.00, 14581.40 117.38, 14615.92 132.94, 14660.63 190.95, 14705.34 108.35, 14750.04 202.06, 14808.34 72.35, 14837.49 166.34, 14872.06 31.72, 14889.35 172.21, 14917.34 105.90, 14945.33 70.12, 14973.33 143.27, 15113.51 69.88, 15156.13 27.71, 15198.74 166.60, 15241.36 63.95, 15287.86 97.64, 15334.36 118.70, 15380.86 128.44, 15426.93 69.11, 15519.07 67.16, 15539.87 143.16, 15581.48 112.88, 15622.13 169.87, 15703.42 111.55, 15746.65 161.66, 15789.87 160.78, 15833.10 58.13, 15873.56 161.81, 15954.48 64.61, 15989.24 63.82, 16006.62 137.02, 16037.85 130.83, 16069.08 107.88, 16100.31 52.40, 16122.55 60.60, 16144.79 94.89, 16167.03 46.10, 16215.18 215.01, 16311.48 70.25, 16389.73 119.79, 16428.86 150.81, 16448.18 83.79, 16467.49 164.75, 16486.81 133.00, 16589.45 47.57, 16626.01 46.95, 16644.29 143.31, 16706.59 123.44, 16737.74 67.06, 16812.44 140.39, 16839.41 163.89, 16893.34 222.58, 16966.91 237.91, 17009.60 114.27, 17052.29 60.39, 17094.98 90.39, 17160.18 275.61, 17199.13 83.12, 17277.03 263.97, 17369.35 128.89, 17415.51 210.10, 17478.67 293.65, 17549.63 187.14, 17585.11 144.70, 17638.94 209.41, 17665.86 209.54, 17784.29 152.24, 17889.70 105.74, 17917.31 150.46, 17944.93 221.96, 17972.55 164.38, 18043.04 152.56, 18078.29 119.74, 18135.42 275.59, 18218.79 303.49, 18252.98 145.14, 18270.08 218.73, 18310.88 333.27, 18392.48 214.02, 18413.55 338.60, 18434.62 300.02, 18455.69 305.55, 18481.78 334.18, 18507.86 342.76, 18533.95 352.28, 18575.93 318.64, 18617.92 288.74, 18659.90 340.63, 18755.48 357.51, 18803.27 393.56, 18843.00 427.94, 18882.72 403.07, 18922.45 311.55, 19026.96 360.53, 19063.99 446.98, 19101.03 417.58, 19138.06 356.24, 19194.56 463.72, 19222.80 426.86, 19321.74 458.01, 19371.21 286.26, 19435.45 364.88, 19467.56 457.23, 19491.95 309.93, 19540.72 396.74, 19653.33 346.86, 19673.89 450.01, 19694.46 350.71, 19715.03 302.04, 19743.06 247.88, 19771.09 426.81, 19799.12 362.73, 19844.22 351.84, 19866.77 376.95, 19974.69 447.38, 20020.83 286.88, 20113.12 282.81, 20132.82 424.06, 20172.22 336.94, 20226.92 410.48, 20290.11 382.76, 20321.71 350.44, 20408.40 331.66, 20451.74 388.33, 20573.39 367.61, 20603.33 325.57, 20633.27 356.91, 20663.21 337.78, 20763.37 247.08, 20832.75 197.39, 21121.90 124.76, 20982.19 -61.58, 20798.06 -116.86, 20763.37 -168.47, 20729.98 -52.33, 20696.60 -203.07, 20663.21 -186.00, 20573.39 -30.02, 20532.84 -165.95, 20492.29 -22.60, 20451.74 -129.49, 20365.05 -86.09, 20321.71 -65.88, 20258.52 -154.37, 20226.92 -114.82, 20208.69 -20.49, 20190.45 -3.53, 20172.22 -105.46, 20152.52 -7.74, 20113.12 0.25, 20066.98 -125.77, 19974.69 -123.17, 19938.72 -110.93, 19902.75 -39.58, 19866.77 -104.22, 19821.67 -73.71, 19799.12 -11.04, 19715.03 -31.87, 19653.33 -123.30, 19615.79 25.12, 19578.26 -163.96, 19540.72 -41.95, 19516.33 7.66, 19467.56 26.66, 19403.33 -25.80, 19371.21 -36.82, 19272.27 9.40, 19222.80 33.66, 19166.31 8.51, 19138.06 33.31, 19026.96 -82.10, 18992.12 48.43, 18957.28 -40.73, 18922.45 40.00, 18803.27 23.34, 18707.69 15.39, 18659.90 -117.22, 18533.95 -104.93, 18455.69 -168.17, 18392.48 -219.45, 18351.68 -74.65, 18270.08 -222.31, 18235.88 -226.63, 18218.79 -141.56, 18191.00 -237.54, 18163.21 -266.47, 18135.42 -281.64, 18116.38 -114.92, 18097.34 -263.10, 18078.29 -239.75, 18007.80 -195.22, 17972.55 -186.69, 17889.70 -140.29, 17854.56 -125.94, 17819.42 -191.78, 17784.29 -309.11, 17744.81 -295.21, 17705.33 -209.14, 17665.86 -148.11, 17612.02 -258.86, 17585.11 -317.77, 17514.15 -248.24, 17478.67 -139.16, 17457.62 -124.29, 17436.56 -144.63, 17415.51 -187.00, 17323.19 -197.04, 17277.03 -136.90, 17238.08 -256.25, 17160.18 -297.68, 17138.45 -176.57, 17116.72 -215.57, 17094.98 -247.58, 16966.91 -327.14, 16942.39 -247.00, 16917.87 -259.58, 16893.34 -281.40, 16866.37 -349.49, 16812.44 -338.01, 16787.54 -331.35, 16762.64 -250.83, 16737.74 -297.81, 16675.44 -372.37, 16644.29 -283.73, 16607.73 -268.10, 16589.45 -298.79, 16555.24 -257.67, 16521.03 -220.99, 16486.81 -272.02, 16428.86 -252.74, 16350.61 -246.61, 16311.48 -240.61, 16263.33 -208.95, 16167.03 -349.02, 16100.31 -366.25, 16006.62 -218.04, 15971.86 -203.03, 15954.48 -309.36, 15914.02 -218.47, 15833.10 -375.99, 15703.42 -299.29, 15662.77 -426.94, 15581.48 -299.60, 15560.68 -324.35, 15519.07 -417.93, 15473.00 -295.77, 15380.86 -228.80, 15241.36 -305.93, 15113.51 -301.64, 15066.78 -359.88, 15020.06 -249.78, 14973.33 -280.32, 14889.35 -348.51, 14854.78 -320.13, 14837.49 -279.75, 14779.19 -361.91, 14750.04 -342.89, 14615.92 -227.53, 14598.66 -361.67, 14564.14 -227.34, 14525.09 -220.23, 14447.00 -277.92, 14369.84 -309.73, 14331.26 -323.70, 14297.14 -331.23, 14263.01 -216.72, 14228.89 -306.79, 14183.54 -276.96, 14160.86 -399.22, 14137.01 -230.28, 14113.16 -276.62, 14089.30 -321.90, 14054.01 -204.90, 13983.43 -354.91, 13958.26 -263.69, 13933.10 -211.75, 13907.94 -247.47, 13849.70 -414.12, 13820.57 -423.30, 13795.32 -335.49, 13744.81 -282.66, 13654.23 -267.05, 13608.94 -245.68, 13585.48 -237.18, 13538.56 -324.89, 13454.90 -228.26, 13421.98 -331.02, 13356.15 -278.75, 13324.68 -375.62, 13293.22 -359.74, 13261.75 -358.22, 13230.27 -353.48, 13198.78 -169.63, 13167.29 -280.16, 13118.99 -324.02, 13094.84 -312.68, 13051.33 -218.48, 12964.32 -385.06, 12874.06 -233.73, 12833.96 -315.06, 12793.85 -325.01, 12753.74 -250.98, 12661.33 -239.50, 12615.12 -177.09, 12582.26 -181.68, 12549.41 -240.73, 12516.55 -128.93, 12463.70 -318.56, 12400.64 -218.12, 12369.11 -244.16, 12275.78 -106.73, 12227.24 -95.46, 12130.15 -157.39, 12110.85 -256.63, 12091.56 -158.36, 12072.27 -206.47, 11927.84 -196.30, 11858.95 -139.87, 11824.50 -291.28, 11794.04 -311.14, 11763.57 -261.35, 11733.10 -316.75, 11701.43 -173.08, 11669.76 -139.34, 11638.09 -291.45, 11600.65 -289.67, 11563.21 -235.16, 11525.77 -152.98, 11504.77 -202.06, 11483.77 -178.54, 11462.76 -275.00, 11425.49 -325.85, 11350.95 -225.22, 11307.84 -290.65, 11286.29 -311.51, 11265.74 -329.51, 11245.18 -224.58, 11224.63 -184.14, 11174.84 -301.54, 11125.04 -255.87, 11075.25 -199.20, 11050.92 -305.18, 11002.24 -292.23, 10976.40 -174.95, 10950.56 -126.38, 10924.71 -125.61, 10896.44 -253.25, 10839.91 -136.31, 10696.45 -135.55, 10670.27 -229.40, 10644.09 -163.99, 10617.91 -269.10, 10519.18 -162.93, 10469.81 -192.65, 10404.78 -133.03, 10372.26 -123.31, 10345.16 -252.58, 10318.05 -301.38, 10290.94 -335.07, 10265.45 -325.03, 10239.97 -203.19, 10214.48 -186.23, 10188.46 -163.58, 10162.44 -342.45, 10136.42 -352.51, 10107.88 -183.70, 10050.81 -175.92, 10006.68 -179.25, 9918.42 -279.74, 9829.22 -280.74, 9686.04 -294.19, 9658.81 -208.63, 9604.37 -175.35, 9572.77 -252.10, 9541.18 -307.69, 9509.59 -187.62, 9469.61 -255.87, 9449.62 -356.34, 9407.12 -235.16, 9364.62 -182.34, 9322.12 -279.40, 9287.74 -218.25, 9253.35 -305.83, 9218.97 -338.13, 9184.62 -279.00, 9150.26 -284.47, 9115.91 -225.35, 8973.16 -345.91, 8941.12 -311.13, 8909.09 -257.95, 8877.06 -163.12, 8797.97 -301.10, 8705.44 -331.67, 8602.98 -328.96, 8569.29 -212.51, 8552.44 -251.70, 8496.34 -251.93, 8468.29 -264.59, 8421.80 -126.09, 8328.82 -258.43, 8279.36 -283.14, 8180.42 -158.14, 8136.77 -287.97, 8114.94 -115.36, 8020.24 -235.31, 7972.89 -227.80, 7882.72 -304.81, 7844.46 -339.15, 7825.33 -228.28, 7717.42 -252.27, 7699.96 -292.39, 7682.49 -177.48, 7665.02 -336.74, 7638.62 -227.55, 7585.82 -268.51, 7552.30 -193.07, 7485.24 -360.59, 7412.55 -317.34, 7350.22 -287.26, 7319.05 -296.47, 7280.93 -223.25, 7242.81 -224.58, 7204.68 -356.86, 7123.33 -220.51, 7082.65 -288.60, 6940.98 -303.01, 6906.94 -399.38, 6838.85 -220.44, 6785.31 -268.78, 6654.81 -296.00, 6603.50 -202.92, 6581.53 -331.36, 6559.57 -273.68, 6537.61 -213.73, 6494.49 -266.12, 6472.92 -186.21, 6445.99 -154.46, 6392.13 -136.71, 6361.82 -189.72, 6331.51 -263.37, 6301.21 -286.15, 6242.52 -301.34, 6213.18 -190.00, 6135.05 -323.08, 6095.99 -154.64, 6054.72 -249.85, 6013.45 -227.89, 5972.19 -217.40, 5929.70 -233.19, 5887.22 -182.62, 5844.73 -231.60, 5797.49 -237.34, 5703.01 -309.08, 5615.44 -243.66, 5595.71 -294.11, 5556.23 -189.11, 5477.51 -241.76, 5425.60 -228.72, 5399.64 -150.21, 5338.70 -193.63, 5310.40 -340.39, 5282.10 -214.98, 5253.80 -275.76, 5206.95 -214.89, 5113.25 -302.15, 5083.21 -124.65, 5023.12 -296.92, 5003.96 -259.77, 4965.65 -209.27, 4909.10 -255.40, 4880.83 -261.77, 4737.95 -306.46, 4697.92 -288.31, 4657.90 -312.02, 4617.87 -248.40, 4569.14 -279.86, 4520.40 -281.20, 4471.67 -176.00, 4373.62 -183.58, 4348.29 -232.31, 4297.62 -180.32, 4279.46 -265.88, 4261.29 -186.81, 4243.13 -169.84, 4167.80 -169.83, 4130.14 -180.81, 4090.75 -144.17, 4051.36 -253.44, 4011.98 -160.00, 3878.31 -194.88, 3835.08 -229.28, 3748.62 -346.10, 3720.04 -317.45, 3691.46 -294.93, 3662.88 -346.58, 3611.99 -256.70, 3586.55 -216.01, 3493.33 -374.62, 3405.51 -152.36, 3361.61 -359.93, 3236.47 -321.74, 3210.77 -252.68, 3185.06 -291.97, 3159.36 -297.70, 3129.25 -173.83, 3099.15 -255.86, 3069.05 -263.91, 2929.50 -174.31, 2873.88 -280.01, 2804.60 -264.58, 2769.96 -71.91, 2744.02 -150.13, 2692.14 -72.07, 2544.18 -203.82, 2499.79 -144.96, 2411.01 -122.95, 2319.96 -237.70, 2278.97 -232.95, 2196.98 -78.65, 2148.69 -214.62, 2100.39 -207.50, 2052.10 -231.17, 1997.74 -228.65, 1960.11 -128.19, 1884.86 -201.39, 1840.26 -117.72, 1751.08 -188.53, 1702.33 -235.82, 1653.59 -63.17, 1604.85 -73.79, 1558.63 -91.32, 1512.42 -196.39, 1466.21 -214.71, 1424.26 -190.51, 1382.31 -141.63, 1340.35 -127.48, 1210.37 -259.20, 1190.30 -213.70, 1150.16 -64.57, 1114.26 -74.73, 1042.47 -117.91, 983.53 -56.23, 954.05 -250.94, 926.89 -114.78, 899.73 -188.77, 872.57 -115.31, 801.16 -172.03, 781.71 -83.65, 742.81 -163.26, 686.34 -165.82, 658.11 -247.72, 567.66 -208.46, 518.32 -146.06, 468.99 -100.66, 419.66 -189.29, 355.32 -174.93, 323.15 -289.90, 279.24 -231.08, 191.42 -291.89, 51.61 -186.08, -87.40 -245.18, -29.42 212.44))'
    q_wkt = 'POLYGON ((-11.20 67.39, 17.20 82.22, 34.41 107.42, 51.61 66.80, 98.21 47.30, 144.81 23.28, 191.42 62.71, 235.33 61.16, 323.15 51.89, 387.49 56.63, 419.66 122.98, 567.66 130.54, 597.81 95.76, 627.96 82.10, 658.11 103.23, 714.58 131.77, 742.81 117.09, 762.26 114.83, 801.16 160.10, 824.96 123.17, 848.77 112.09, 872.57 145.11, 954.05 95.57, 1013.00 111.39, 1042.47 148.24, 1078.37 167.17, 1150.16 153.17, 1170.23 153.46, 1210.37 118.52, 1253.70 129.77, 1297.03 90.38, 1340.35 147.27, 1466.21 83.18, 1604.85 101.46, 1751.08 154.05, 1795.67 128.91, 1884.86 142.52, 1922.49 111.63, 1997.74 97.12, 2015.86 80.67, 2033.98 125.17, 2052.10 119.24, 2196.98 120.22, 2237.98 162.78, 2319.96 185.12, 2350.31 161.69, 2380.66 136.51, 2411.01 130.17, 2455.40 156.37, 2544.18 147.06, 2593.50 105.12, 2642.82 109.62, 2692.14 139.16, 2718.08 123.18, 2769.96 132.54, 2839.24 106.22, 2873.88 99.55, 2892.42 93.11, 2910.96 104.21, 2929.50 93.17, 2976.02 79.62, 3022.53 54.47, 3069.05 28.24, 3159.36 17.39, 3236.47 6.70, 3278.18 -15.08, 3319.89 23.98, 3361.61 54.44, 3449.42 -3.56, 3493.33 -11.43, 3524.40 -8.09, 3555.47 42.01, 3586.55 19.33, 3637.44 22.53, 3662.88 40.20, 3748.62 13.57, 3791.85 19.22, 3878.31 50.70, 3922.87 36.47, 3967.42 2.56, 4011.98 47.48, 4130.14 30.55, 4205.47 34.57, 4243.13 14.44, 4297.62 13.67, 4322.95 49.09, 4373.62 14.75, 4406.30 17.69, 4438.98 17.57, 4471.67 82.79, 4617.87 64.14, 4737.95 55.03, 4785.58 108.90, 4833.21 83.21, 4880.83 100.64, 4937.38 25.62, 4965.65 64.40, 4984.81 45.45, 5023.12 72.68, 5053.17 48.43, 5113.25 88.86, 5160.10 66.16, 5253.80 28.33, 5338.70 5.32, 5359.01 -2.55, 5379.33 39.26, 5399.64 20.03, 5451.55 8.78, 5477.51 95.82, 5503.75 86.71, 5529.99 32.80, 5556.23 82.06, 5575.97 30.66, 5615.44 43.97, 5644.63 44.31, 5673.82 63.16, 5703.01 90.89, 5750.25 45.91, 5844.73 98.82, 5972.19 34.62, 6095.99 10.61, 6174.11 20.62, 6213.18 37.86, 6271.86 24.66, 6301.21 67.42, 6392.13 90.92, 6419.06 46.04, 6472.92 63.32, 6516.05 -3.49, 6537.61 -4.42, 6603.50 29.39, 6620.60 -41.79, 6637.70 -42.61, 6654.81 5.25, 6698.31 -20.25, 6741.81 -64.75, 6785.31 -51.32, 6803.16 -43.80, 6821.00 -63.66, 6838.85 -5.50, 6872.89 -54.97, 6940.98 -56.37, 6988.21 -40.48, 7035.43 10.33, 7082.65 -10.41, 7164.01 -62.79, 7204.68 -57.34, 7319.05 -23.53, 7381.38 4.81, 7412.55 -27.04, 7436.78 8.98, 7461.01 -11.22, 7485.24 21.62, 7518.77 -18.37, 7585.82 29.20, 7612.22 35.62, 7665.02 17.37, 7717.42 10.65, 7753.39 28.41, 7789.36 54.64, 7825.33 40.61, 7863.59 -3.85, 7882.72 55.55, 7912.78 19.24, 7942.83 62.94, 7972.89 100.12, 8067.59 50.70, 8114.94 88.58, 8158.60 69.61, 8180.42 89.24, 8229.89 39.37, 8328.82 57.77, 8375.31 84.58, 8468.29 32.51, 8524.39 11.29, 8552.44 27.89, 8586.13 26.40, 8602.98 56.91, 8637.13 -20.18, 8671.29 -17.38, 8705.44 18.49, 8736.28 24.27, 8767.12 6.91, 8797.97 59.15, 8824.33 28.86, 8850.69 65.58, 8877.06 13.77, 8973.16 44.94, 9020.74 14.15, 9068.32 -38.30, 9115.91 5.50, 9218.97 46.80, 9322.12 -10.16, 9449.62 -20.46, 9489.60 -49.84, 9509.59 -25.12, 9604.37 57.98, 9631.59 14.84, 9686.04 65.13, 9733.76 19.57, 9781.49 37.59, 9829.22 23.64, 9858.96 31.63, 9888.69 -22.74, 9918.42 -17.22, 9962.55 37.74, 10050.81 40.43, 10079.34 15.24, 10136.42 11.33, 10214.48 37.37, 10290.94 23.48, 10372.26 56.13, 10437.30 49.28, 10469.81 67.87, 10568.55 73.82, 10617.91 104.78, 10696.45 82.25, 10744.27 57.69, 10792.09 100.18, 10839.91 87.76, 10868.17 68.31, 10924.71 75.13, 11002.24 66.50, 11026.58 32.68, 11075.25 53.97, 11224.63 24.69, 11286.29 44.41, 11329.40 22.34, 11350.95 11.75, 11388.22 23.32, 11462.76 26.74, 11525.77 7.40, 11638.09 84.90, 11733.10 65.18, 11824.50 71.84, 11893.39 66.55, 11927.84 54.70, 11975.98 94.26, 12024.12 93.38, 12072.27 71.33, 12130.15 113.47, 12178.69 98.18, 12275.78 53.82, 12306.89 31.11, 12338.00 71.47, 12369.11 45.29, 12432.17 72.67, 12463.70 60.16, 12481.32 95.79, 12498.93 71.38, 12516.55 56.02, 12615.12 46.84, 12707.53 13.94, 12753.74 56.42, 12874.06 19.65, 12904.15 -37.43, 12934.23 -43.78, 12964.32 23.79, 13007.82 -21.43, 13094.84 5.05, 13143.14 17.69, 13167.29 18.17, 13261.75 -18.91, 13356.15 -29.12, 13389.06 -64.55, 13454.90 -8.15, 13482.78 -45.84, 13510.67 -13.73, 13538.56 -4.03, 13562.02 2.57, 13608.94 -4.94, 13699.52 -31.27, 13744.81 -49.46, 13770.06 -54.88, 13820.57 -36.44, 13878.82 -55.38, 13907.94 -43.89, 13983.43 3.25, 14018.72 -17.62, 14089.30 -23.61, 14160.86 -28.87, 14206.21 -54.78, 14228.89 -43.22, 14331.26 -9.46, 14408.42 -34.28, 14447.00 -54.37, 14486.04 -32.52, 14564.14 -16.60, 14581.40 -16.66, 14615.92 3.82, 14660.63 8.66, 14705.34 -5.81, 14750.04 30.18, 14808.34 -33.75, 14837.49 -8.22, 14872.06 -56.31, 14889.35 -13.66, 14917.34 -52.83, 14945.33 -66.82, 14973.33 -17.76, 15113.51 -40.80, 15156.13 -49.71, 15198.74 0.78, 15241.36 -46.48, 15287.86 -27.10, 15334.36 -31.12, 15380.86 -28.33, 15426.93 -66.55, 15519.07 -63.29, 15539.87 -49.33, 15581.48 -49.54, 15622.13 -27.33, 15703.42 -30.68, 15746.65 -27.29, 15789.87 -4.38, 15833.10 -32.26, 15873.56 -6.09, 15954.48 -21.98, 15989.24 -24.02, 16006.62 8.66, 16037.85 13.31, 16069.08 1.92, 16100.31 -19.16, 16122.55 -15.17, 16144.79 -14.26, 16167.03 -20.86, 16215.18 50.78, 16311.48 -15.67, 16389.73 2.49, 16428.86 6.96, 16448.18 -30.26, 16467.49 -0.24, 16486.81 -4.26, 16589.45 -19.64, 16626.01 -22.23, 16644.29 11.40, 16706.59 -10.44, 16737.74 -20.10, 16812.44 3.45, 16839.41 -7.13, 16893.34 26.65, 16966.91 48.19, 17009.60 -10.06, 17052.29 -15.53, 17094.98 2.56, 17160.18 73.46, 17199.13 15.18, 17277.03 88.44, 17369.35 37.61, 17415.51 66.71, 17478.67 102.50, 17549.63 60.00, 17585.11 50.12, 17638.94 68.30, 17665.86 81.24, 17784.29 54.01, 17889.70 39.34, 17917.31 51.76, 17944.93 81.10, 17972.55 61.45, 18043.04 34.63, 18078.29 49.03, 18135.42 110.79, 18218.79 132.65, 18252.98 70.60, 18270.08 108.51, 18310.88 144.43, 18392.48 118.51, 18413.55 153.29, 18434.62 155.21, 18455.69 169.94, 18481.78 168.10, 18507.86 185.30, 18533.95 186.69, 18575.93 190.23, 18617.92 178.76, 18659.90 202.14, 18755.48 217.77, 18803.27 231.03, 18843.00 242.28, 18882.72 235.11, 18922.45 222.52, 19026.96 234.92, 19063.99 268.87, 19101.03 246.34, 19138.06 227.91, 19194.56 268.61, 19222.80 264.07, 19321.74 255.34, 19371.21 199.11, 19435.45 212.10, 19467.56 264.40, 19491.95 211.92, 19540.72 229.29, 19653.33 218.84, 19673.89 273.27, 19694.46 223.54, 19715.03 210.44, 19743.06 178.72, 19771.09 232.18, 19799.12 220.56, 19844.22 210.43, 19866.77 230.85, 19974.69 239.37, 20020.83 193.31, 20113.12 193.76, 20132.82 241.63, 20172.22 213.84, 20226.92 236.04, 20290.11 231.38, 20321.71 205.53, 20408.40 198.57, 20451.74 211.80, 20573.39 186.26, 20603.33 167.69, 20633.27 178.66, 20663.21 181.98, 20763.37 136.93, 20832.75 121.36, 20964.68 96.90, 20906.62 26.23, 20798.06 26.83, 20763.37 -28.22, 20729.98 23.53, 20696.60 -21.33, 20663.21 -10.88, 20573.39 47.47, 20532.84 21.63, 20492.29 62.42, 20451.74 24.03, 20365.05 54.98, 20321.71 55.32, 20258.52 43.54, 20226.92 49.77, 20208.69 87.17, 20190.45 101.55, 20172.22 52.01, 20152.52 82.85, 20113.12 89.36, 20066.98 66.39, 19974.69 35.79, 19938.72 40.45, 19902.75 73.78, 19866.77 36.52, 19821.67 85.16, 19799.12 86.43, 19715.03 80.80, 19653.33 48.77, 19615.79 99.21, 19578.26 40.95, 19540.72 73.94, 19516.33 107.69, 19467.56 104.78, 19403.33 75.44, 19371.21 79.34, 19272.27 115.57, 19222.80 123.85, 19166.31 111.86, 19138.06 115.23, 19026.96 80.93, 18992.12 131.08, 18957.28 99.61, 18922.45 109.49, 18803.27 100.91, 18707.69 90.82, 18659.90 24.63, 18533.95 15.30, 18455.69 -14.43, 18392.48 -47.11, 18351.68 7.81, 18270.08 -58.33, 18235.88 -54.59, 18218.79 -24.19, 18191.00 -65.91, 18163.21 -78.77, 18135.42 -96.82, 18116.38 -32.70, 18097.34 -86.28, 18078.29 -93.95, 18007.80 -74.66, 17972.55 -72.36, 17889.70 -57.79, 17854.56 -54.61, 17819.42 -79.50, 17784.29 -106.26, 17744.81 -96.82, 17705.33 -72.05, 17665.86 -57.12, 17612.02 -91.69, 17585.11 -122.77, 17514.15 -70.33, 17478.67 -63.49, 17457.62 -61.38, 17436.56 -62.00, 17415.51 -88.36, 17323.19 -75.21, 17277.03 -57.40, 17238.08 -102.20, 17160.18 -127.37, 17138.45 -86.74, 17116.72 -95.64, 17094.98 -121.85, 16966.91 -159.95, 16942.39 -134.48, 16917.87 -131.81, 16893.34 -155.89, 16866.37 -165.72, 16812.44 -163.03, 16787.54 -150.70, 16762.64 -118.04, 16737.74 -155.29, 16675.44 -184.03, 16644.29 -143.53, 16607.73 -132.60, 16589.45 -153.23, 16555.24 -136.98, 16521.03 -121.34, 16486.81 -165.00, 16428.86 -142.42, 16350.61 -122.46, 16311.48 -122.85, 16263.33 -99.13, 16167.03 -162.61, 16100.31 -173.28, 16006.62 -121.46, 15971.86 -114.17, 15954.48 -163.00, 15914.02 -124.32, 15833.10 -198.96, 15703.42 -195.64, 15662.77 -232.09, 15581.48 -194.21, 15560.68 -213.69, 15519.07 -253.33, 15473.00 -196.86, 15380.86 -157.63, 15241.36 -174.24, 15113.51 -178.36, 15066.78 -196.76, 15020.06 -167.31, 14973.33 -183.25, 14889.35 -212.23, 14854.78 -190.27, 14837.49 -176.66, 14779.19 -170.59, 14750.04 -176.06, 14615.92 -140.80, 14598.66 -185.22, 14564.14 -146.72, 14525.09 -148.86, 14447.00 -179.29, 14369.84 -182.25, 14331.26 -190.02, 14297.14 -183.19, 14263.01 -142.30, 14228.89 -181.62, 14183.54 -171.95, 14160.86 -240.08, 14137.01 -154.29, 14113.16 -167.66, 14089.30 -184.42, 14054.01 -132.62, 13983.43 -199.03, 13958.26 -159.89, 13933.10 -147.51, 13907.94 -176.85, 13849.70 -238.56, 13820.57 -215.33, 13795.32 -200.98, 13744.81 -164.69, 13654.23 -159.02, 13608.94 -155.02, 13585.48 -136.97, 13538.56 -167.92, 13454.90 -150.43, 13421.98 -177.69, 13356.15 -176.51, 13324.68 -197.75, 13293.22 -179.58, 13261.75 -166.28, 13230.27 -165.69, 13198.78 -99.25, 13167.29 -135.21, 13118.99 -142.25, 13094.84 -138.89, 13051.33 -115.54, 12964.32 -214.21, 12874.06 -134.02, 12833.96 -157.33, 12793.85 -156.37, 12753.74 -133.73, 12661.33 -118.15, 12615.12 -92.93, 12582.26 -76.82, 12549.41 -109.47, 12516.55 -58.85, 12463.70 -130.17, 12400.64 -89.62, 12369.11 -98.15, 12275.78 -35.72, 12227.24 -32.28, 12130.15 -59.44, 12110.85 -86.60, 12091.56 -56.57, 12072.27 -75.66, 11927.84 -80.27, 11858.95 -54.48, 11824.50 -120.32, 11794.04 -124.43, 11763.57 -118.27, 11733.10 -139.99, 11701.43 -77.33, 11669.76 -62.03, 11638.09 -111.31, 11600.65 -127.35, 11563.21 -105.89, 11525.77 -89.75, 11504.77 -99.87, 11483.77 -95.42, 11462.76 -127.63, 11425.49 -122.19, 11350.95 -102.97, 11307.84 -117.11, 11286.29 -138.91, 11265.74 -144.98, 11245.18 -113.95, 11224.63 -102.62, 11174.84 -127.94, 11125.04 -106.77, 11075.25 -90.72, 11050.92 -135.52, 11002.24 -111.85, 10976.40 -56.41, 10950.56 -37.75, 10924.71 -55.11, 10896.44 -86.54, 10839.91 -64.03, 10696.45 -56.36, 10670.27 -76.89, 10644.09 -66.47, 10617.91 -97.19, 10519.18 -37.52, 10469.81 -65.22, 10404.78 -50.90, 10372.26 -56.13, 10345.16 -110.14, 10318.05 -114.42, 10290.94 -141.40, 10265.45 -128.86, 10239.97 -104.93, 10214.48 -95.04, 10188.46 -96.80, 10162.44 -139.19, 10136.42 -168.22, 10107.88 -116.78, 10050.81 -101.82, 10006.68 -92.24, 9918.42 -142.26, 9829.22 -149.20, 9686.04 -137.55, 9658.81 -98.21, 9604.37 -100.62, 9572.77 -140.53, 9541.18 -149.25, 9509.59 -128.97, 9469.61 -136.14, 9449.62 -178.73, 9407.12 -128.67, 9364.62 -99.49, 9322.12 -140.98, 9287.74 -128.60, 9253.35 -138.91, 9218.97 -152.41, 9184.62 -136.11, 9150.26 -133.20, 9115.91 -120.17, 8973.16 -174.78, 8941.12 -151.25, 8909.09 -115.89, 8877.06 -94.60, 8797.97 -143.30, 8705.44 -150.95, 8602.98 -160.03, 8569.29 -101.43, 8552.44 -124.72, 8496.34 -106.84, 8468.29 -105.88, 8421.80 -64.49, 8328.82 -105.30, 8279.36 -93.54, 8180.42 -55.91, 8136.77 -100.57, 8114.94 -43.35, 8020.24 -84.94, 7972.89 -98.13, 7882.72 -148.62, 7844.46 -153.90, 7825.33 -110.57, 7717.42 -120.42, 7699.96 -119.09, 7682.49 -87.99, 7665.02 -161.69, 7638.62 -114.30, 7585.82 -147.98, 7552.30 -121.27, 7485.24 -179.21, 7412.55 -171.76, 7350.22 -159.95, 7319.05 -168.38, 7280.93 -149.95, 7242.81 -136.56, 7204.68 -190.77, 7123.33 -143.32, 7082.65 -179.05, 6940.98 -175.40, 6906.94 -210.25, 6838.85 -152.03, 6785.31 -156.66, 6654.81 -160.25, 6603.50 -126.54, 6581.53 -151.68, 6559.57 -147.20, 6537.61 -111.79, 6494.49 -142.76, 6472.92 -98.40, 6445.99 -72.63, 6392.13 -65.77, 6361.82 -67.77, 6331.51 -88.68, 6301.21 -115.01, 6242.52 -112.31, 6213.18 -84.89, 6135.05 -136.35, 6095.99 -76.39, 6054.72 -97.12, 6013.45 -96.92, 5972.19 -83.67, 5929.70 -78.38, 5887.22 -63.20, 5844.73 -102.61, 5797.49 -82.08, 5703.01 -118.83, 5615.44 -99.51, 5595.71 -116.94, 5556.23 -73.74, 5477.51 -102.90, 5425.60 -94.37, 5399.64 -82.56, 5338.70 -105.10, 5310.40 -146.84, 5282.10 -107.05, 5253.80 -126.93, 5206.95 -98.31, 5113.25 -126.59, 5083.21 -59.19, 5023.12 -115.85, 5003.96 -84.42, 4965.65 -88.33, 4909.10 -113.51, 4880.83 -105.00, 4737.95 -117.19, 4697.92 -124.73, 4657.90 -113.87, 4617.87 -90.48, 4569.14 -103.85, 4520.40 -94.36, 4471.67 -73.01, 4373.62 -81.49, 4348.29 -108.37, 4297.62 -94.33, 4279.46 -123.42, 4261.29 -94.79, 4243.13 -91.56, 4167.80 -81.76, 4130.14 -82.32, 4090.75 -54.91, 4051.36 -93.43, 4011.98 -80.90, 3878.31 -103.98, 3835.08 -116.15, 3748.62 -166.08, 3720.04 -170.95, 3691.46 -162.53, 3662.88 -163.76, 3611.99 -127.43, 3586.55 -127.89, 3493.33 -184.48, 3405.51 -85.90, 3361.61 -160.89, 3236.47 -153.96, 3210.77 -110.58, 3185.06 -114.93, 3159.36 -123.88, 3129.25 -82.23, 3099.15 -100.98, 3069.05 -105.33, 2929.50 -72.91, 2873.88 -81.59, 2804.60 -72.24, 2769.96 -0.46, 2744.02 -25.41, 2692.14 10.89, 2544.18 -28.10, 2499.79 -4.35, 2411.01 1.23, 2319.96 -62.06, 2278.97 -47.56, 2196.98 9.24, 2148.69 -32.32, 2100.39 -52.60, 2052.10 -46.06, 1997.74 -65.95, 1960.11 -12.40, 1884.86 -43.95, 1840.26 3.35, 1751.08 -36.78, 1702.33 -46.00, 1653.59 19.06, 1604.85 -0.03, 1558.63 -0.56, 1512.42 -46.75, 1466.21 -60.52, 1424.26 -55.27, 1382.31 -37.25, 1340.35 -33.74, 1210.37 -57.99, 1190.30 -42.89, 1150.16 16.74, 1114.26 23.53, 1042.47 3.79, 983.53 20.67, 954.05 -70.49, 926.89 -23.05, 899.73 -46.40, 872.57 -8.63, 801.16 -29.59, 781.71 -2.31, 742.81 -33.61, 686.34 -27.54, 658.11 -61.29, 567.66 -53.58, 518.32 -34.01, 468.99 -13.60, 419.66 -70.72, 355.32 -65.56, 323.15 -93.44, 279.24 -84.63, 191.42 -121.87, 51.61 -77.45, -29.93 -94.19, -11.20 67.39))'
    ccw = False

    #tests_r += [tests(N, p_wkt, q_wkt, '959.406,310.225#1533.276,69.854#2404.150,242.896#1000,2000', True)]

    #3 intersection intervals
    tests_r += [tests(N, p_wkt, q_wkt, '959.406,310.225#1540.827,142.846#2404.150,242.896#1000,2000', True, ccw)]

    #5 intersection intervals
    tests_r += [tests(N, p_wkt, q_wkt, '959.406,310.225#1540.827,168.016#2404.150,242.896#1000,2000', True, ccw)]

    #POLYGON ((-11637.62 1091.43, -11590.99 1166.42, -11573.79 1177.81, -11556.59 1100.97, -11509.98 1082.82, -11463.38 971.31, -11416.78 1073.14, -11372.87 1095.72, -11285.04 1021.18, -11220.70 1013.28, -11188.53 1179.21, -11040.54 1186.78, -11010.39 1061.33, -10980.24 1043.07, -10950.09 1078.22, -10893.62 1190.38, -10865.38 1111.80, -10845.93 1206.97, -10807.04 1209.75, -10783.23 1136.80, -10759.43 1135.32, -10735.62 1210.41, -10654.14 1056.92, -10595.20 1079.79, -10565.72 1181.42, -10529.83 1240.82, -10458.03 1173.80, -10437.96 1216.86, -10397.82 1109.45, -10354.49 1200.72, -10311.17 1067.91, -10267.84 1204.28, -10141.98 1065.58, -10003.35 1055.76, -9857.12 1180.95, -9812.52 1109.24, -9723.34 1156.85, -9685.71 1119.56, -9610.45 1085.37, -9592.33 1059.13, -9574.21 1142.39, -9556.10 1187.76, -9411.21 1106.48, -9370.22 1191.77, -9288.23 1235.16, -9257.88 1171.21, -9227.54 1128.27, -9197.19 1095.28, -9152.80 1220.10, -9064.02 1166.94, -9014.70 1055.82, -8965.38 1063.39, -8916.06 1155.04, -8890.12 1154.25, -8838.24 1160.52, -8768.96 1123.26, -8734.32 1099.15, -8715.78 1165.38, -8697.23 1189.26, -8678.69 1152.07, -8632.18 1126.08, -8585.66 1077.85, -8539.14 980.40, -8448.84 992.53, -8371.72 992.80, -8330.01 944.25, -8288.30 1074.00, -8246.59 1098.00, -8158.77 957.42, -8114.87 961.47, -8083.79 1014.67, -8052.72 1101.39, -8021.65 1094.17, -7970.76 1049.27, -7945.31 1082.29, -7859.57 1034.92, -7816.34 1061.03, -7729.88 1074.13, -7685.33 1051.58, -7640.77 965.44, -7596.22 1050.45, -7478.05 1006.07, -7402.73 1022.16, -7365.07 966.15, -7310.57 994.05, -7285.24 1101.99, -7234.58 973.18, -7201.89 965.15, -7169.21 961.31, -7136.53 1142.34, -6990.32 1098.93, -6870.24 1068.83, -6822.62 1151.00, -6774.99 1125.65, -6727.36 1174.22, -6670.82 1026.35, -6642.55 1075.88, -6623.39 1002.50, -6585.07 1112.54, -6555.03 1099.46, -6494.94 1156.93, -6448.09 1132.54, -6354.39 1036.11, -6269.49 976.80, -6249.18 950.50, -6228.87 1085.17, -6208.55 960.67, -6156.64 960.96, -6130.68 1166.13, -6104.44 1120.04, -6078.20 981.32, -6051.96 1096.22, -6032.23 1003.36, -5992.75 988.90, -5963.56 1008.36, -5934.37 1048.81, -5905.18 1178.93, -5857.94 1042.35, -5763.46 1175.79, -5636.01 989.43, -5512.21 960.15, -5434.08 983.63, -5395.02 1035.79, -5336.33 991.82, -5306.99 1088.91, -5216.07 1139.83, -5189.14 1090.74, -5135.27 1135.18, -5092.15 991.61, -5070.59 941.93, -5004.70 1087.42, -4987.59 903.47, -4970.49 925.98, -4953.38 1060.40, -4909.88 1028.19, -4866.38 889.47, -4822.88 920.69, -4805.04 931.99, -4787.19 888.79, -4769.35 1036.72, -4735.30 919.42, -4667.21 898.23, -4619.99 950.77, -4572.76 1075.85, -4525.54 1019.14, -4444.19 901.64, -4403.51 899.67, -4289.14 938.95, -4226.81 1055.09, -4195.65 938.93, -4171.41 1050.09, -4147.18 1017.80, -4122.95 1053.22, -4089.42 992.96, -4022.37 1080.45, -3995.97 1085.15, -3943.18 1018.59, -3890.77 972.34, -3854.80 1031.02, -3818.83 1066.49, -3782.86 1071.77, -3744.61 948.11, -3725.48 1041.98, -3695.42 993.32, -3665.36 1117.96, -3635.30 1174.51, -3540.60 1016.81, -3493.25 1108.79, -3449.60 1054.08, -3427.77 1087.75, -3378.31 1018.86, -3279.37 1059.88, -3232.88 1150.94, -3139.90 1008.78, -3083.80 966.00, -3055.75 1047.45, -3022.06 1038.48, -3005.21 1117.65, -2971.06 959.44, -2936.91 969.90, -2902.75 1085.72, -2871.91 1066.96, -2841.07 1014.84, -2810.23 1089.78, -2783.87 1016.00, -2757.50 1129.40, -2731.14 1002.69, -2635.04 1127.81, -2587.45 1102.71, -2539.87 911.77, -2492.29 1026.67, -2389.22 1106.68, -2286.08 974.84, -2158.57 943.69, -2118.59 905.80, -2098.61 929.18, -2003.83 1109.99, -1976.60 1002.32, -1922.16 1115.13, -1874.43 1062.65, -1826.70 1094.64, -1778.97 1064.07, -1749.24 1082.04, -1719.51 959.46, -1689.77 948.78, -1645.64 1068.81, -1557.39 1112.33, -1528.85 1035.28, -1471.78 1006.19, -1393.71 1107.08, -1317.26 985.77, -1235.93 1057.14, -1170.90 1027.32, -1138.38 1063.56, -1039.65 1093.20, -990.28 1150.12, -911.74 1135.77, -863.92 1043.46, -816.11 1155.42, -768.29 1126.88, -740.02 1144.51, -683.48 1117.30, -605.95 1060.79, -581.61 1031.37, -532.94 1098.14, -383.57 1040.70, -321.90 1096.97, -278.80 1044.77, -257.24 970.74, -219.97 1043.02, -145.43 1033.00, -82.42 955.51, 29.89 1166.63, 124.91 1135.58, 216.31 1111.72, 285.20 1079.43, 319.64 1022.75, 367.79 1100.28, 415.93 1138.10, 464.07 1061.67, 521.96 1186.39, 570.50 1139.04, 667.58 1017.22, 698.70 992.13, 729.81 1104.46, 760.92 1026.05, 823.98 1140.65, 855.51 1080.30, 873.12 1146.15, 890.74 1110.41, 908.36 1038.48, 1006.92 1100.70, 1099.34 1014.16, 1145.55 1109.58, 1265.87 1060.59, 1295.95 942.82, 1326.04 914.95, 1356.12 1072.15, 1399.63 938.28, 1486.64 976.57, 1534.95 1029.77, 1559.10 1077.44, 1653.56 945.33, 1747.95 950.79, 1780.87 914.10, 1846.70 1001.34, 1874.59 947.18, 1902.48 1028.64, 1930.37 1000.13, 1953.83 1038.86, 2000.74 1036.98, 2091.33 990.21, 2136.62 939.17, 2161.87 959.91, 2212.38 1011.35, 2270.62 948.90, 2299.74 987.04, 2375.23 1051.59, 2410.52 1019.42, 2481.11 1017.05, 2552.67 1009.77, 2598.02 960.84, 2620.70 954.10, 2723.07 1045.53, 2800.22 1021.47, 2838.80 920.45, 2877.85 978.13, 2955.94 981.98, 2973.20 996.36, 3007.73 1011.92, 3052.44 1069.94, 3097.14 987.33, 3141.85 1081.05, 3200.15 951.34, 3229.30 1045.32, 3263.87 910.70, 3281.15 1051.20, 3309.15 984.89, 3337.14 949.11, 3365.13 1022.25, 3505.32 948.86, 3547.93 906.69, 3590.55 1045.59, 3633.16 942.94, 3679.66 976.62, 3726.16 997.69, 3772.67 1007.42, 3818.74 948.09, 3910.88 946.15, 3931.68 1022.15, 3973.28 991.87, 4013.93 1048.86, 4095.23 990.53, 4138.45 1040.65, 4181.68 1039.77, 4224.90 937.12, 4265.36 1040.80, 4346.29 943.60, 4381.05 942.81, 4398.42 1016.00, 4429.66 1009.82, 4460.89 986.86, 4492.12 931.39, 4514.36 939.58, 4536.60 973.88, 4558.83 925.09, 4606.99 1093.99, 4703.29 949.23, 4781.54 998.77, 4820.66 1029.79, 4839.98 962.78, 4859.30 1043.74, 4878.62 1011.98, 4981.26 926.56, 5017.82 925.94, 5036.10 1022.30, 5098.39 1002.42, 5129.54 946.05, 5204.25 1019.38, 5231.21 1042.87, 5285.15 1101.56, 5358.72 1116.90, 5401.41 993.25, 5444.10 939.38, 5486.79 969.38, 5551.99 1154.60, 5590.94 962.11, 5668.84 1142.96, 5761.16 1007.88, 5807.32 1089.09, 5870.48 1172.64, 5941.43 1066.13, 5976.91 1023.68, 6030.75 1088.40, 6057.66 1088.53, 6176.09 1031.23, 6281.50 984.73, 6309.12 1029.45, 6336.74 1100.95, 6364.35 1043.37, 6434.85 1031.54, 6470.10 998.72, 6527.23 1154.57, 6610.59 1182.48, 6644.79 1024.12, 6661.89 1097.72, 6702.69 1212.26, 6784.28 1093.00, 6805.35 1217.58, 6826.43 1179.01, 6847.50 1184.53, 6873.58 1213.17, 6899.67 1221.75, 6925.75 1231.27, 6967.74 1197.62, 7009.72 1167.73, 7051.71 1219.62, 7147.29 1236.50, 7195.07 1272.55, 7234.80 1306.93, 7274.53 1282.06, 7314.25 1190.54, 7418.76 1239.52, 7455.80 1325.97, 7492.83 1296.57, 7529.87 1235.22, 7586.36 1342.70, 7614.61 1305.84, 7713.55 1337.00, 7763.02 1165.24, 7827.25 1243.87, 7859.37 1336.22, 7883.75 1188.92, 7932.53 1275.72, 8045.13 1225.85, 8065.70 1329.00, 8086.27 1229.69, 8106.84 1181.03, 8134.87 1126.86, 8162.90 1305.80, 8190.93 1241.72, 8236.03 1230.83, 8258.58 1255.93, 8366.49 1326.36, 8412.64 1165.86, 8504.93 1161.79, 8524.63 1303.04, 8564.02 1215.93, 8618.73 1289.47, 8681.92 1261.75, 8713.51 1229.42, 8800.20 1210.65, 8843.55 1267.31, 8965.19 1246.60, 8995.13 1204.56, 9025.07 1235.89, 9055.02 1216.77, 9155.18 1126.06, 9224.56 1076.37, 9513.71 1003.75, 9373.99 817.40, 9189.87 762.12, 9155.18 710.52, 9121.79 826.66, 9088.40 675.91, 9055.02 692.99, 8965.19 848.96, 8924.64 713.03, 8884.09 856.38, 8843.55 749.50, 8756.86 792.90, 8713.51 813.11, 8650.32 724.62, 8618.73 764.17, 8600.49 858.49, 8582.26 875.46, 8564.02 773.52, 8544.32 871.25, 8504.93 879.23, 8458.78 753.22, 8366.49 755.82, 8330.52 768.05, 8294.55 839.41, 8258.58 774.76, 8213.48 805.27, 8190.93 867.95, 8106.84 847.12, 8045.13 755.69, 8007.60 904.10, 7970.06 715.03, 7932.53 837.03, 7908.14 886.65, 7859.37 905.65, 7795.14 853.18, 7763.02 842.16, 7664.08 888.38, 7614.61 912.64, 7558.12 887.50, 7529.87 912.30, 7418.76 796.89, 7383.93 927.41, 7349.09 838.25, 7314.25 918.98, 7195.07 902.33, 7099.50 894.38, 7051.71 761.77, 6925.75 774.05, 6847.50 710.81, 6784.28 659.54, 6743.48 804.34, 6661.89 656.68, 6627.69 652.36, 6610.59 737.43, 6582.80 641.44, 6555.02 612.52, 6527.23 597.35, 6508.19 764.07, 6489.14 615.88, 6470.10 639.23, 6399.60 683.76, 6364.35 692.29, 6281.50 738.70, 6246.37 753.04, 6211.23 687.20, 6176.09 569.87, 6136.62 583.77, 6097.14 669.85, 6057.66 730.88, 6003.83 620.13, 5976.91 561.21, 5905.96 630.75, 5870.48 739.82, 5849.42 754.69, 5828.37 734.36, 5807.32 691.98, 5715.00 681.95, 5668.84 742.09, 5629.89 622.73, 5551.99 581.31, 5530.25 702.42, 5508.52 663.42, 5486.79 631.41, 5358.72 551.84, 5334.20 631.99, 5309.67 619.41, 5285.15 597.59, 5258.18 529.49, 5204.25 540.98, 5179.35 547.63, 5154.44 628.15, 5129.54 581.18, 5067.25 506.62, 5036.10 595.25, 4999.54 610.88, 4981.26 580.20, 4947.05 621.31, 4912.83 658.00, 4878.62 606.97, 4820.66 626.25, 4742.41 632.37, 4703.29 638.38, 4655.14 670.04, 4558.83 529.96, 4492.12 512.74, 4398.42 660.95, 4363.67 675.95, 4346.29 569.63, 4305.83 660.52, 4224.90 503.00, 4095.23 579.69, 4054.58 452.05, 3973.28 579.39, 3952.48 554.63, 3910.88 461.05, 3864.81 583.22, 3772.67 650.19, 3633.16 573.05, 3505.32 577.35, 3458.59 519.10, 3411.86 629.21, 3365.13 598.66, 3281.15 530.47, 3246.58 558.86, 3229.30 599.23, 3171.00 517.08, 3141.85 536.10, 3007.73 651.45, 2990.47 517.31, 2955.94 651.65, 2916.90 658.76, 2838.80 601.06, 2761.64 569.26, 2723.07 555.29, 2688.94 547.75, 2654.82 662.26, 2620.70 572.20, 2575.34 602.02, 2552.67 479.77, 2528.82 648.71, 2504.96 602.37, 2481.11 557.09, 2445.82 674.09, 2375.23 524.07, 2350.07 615.30, 2324.91 667.24, 2299.74 631.51, 2241.50 464.87, 2212.38 455.68, 2187.13 543.50, 2136.62 596.32, 2046.03 611.94, 2000.74 633.30, 1977.29 641.81, 1930.37 554.10, 1846.70 650.72, 1813.79 547.97, 1747.95 600.24, 1716.49 503.37, 1685.02 519.25, 1653.56 520.77, 1622.07 525.50, 1590.58 709.35, 1559.10 598.83, 1510.79 554.96, 1486.64 566.31, 1443.14 660.51, 1356.12 493.93, 1265.87 645.26, 1225.76 563.93, 1185.65 553.97, 1145.55 628.01, 1053.13 639.49, 1006.92 701.90, 974.07 697.31, 941.21 638.26, 908.36 750.06, 855.51 560.43, 792.45 660.86, 760.92 634.82, 667.58 772.25, 619.04 783.53, 521.96 721.60, 502.66 622.35, 483.37 720.63, 464.07 672.52, 319.64 682.69, 250.75 739.12, 216.31 587.70, 185.84 567.85, 155.38 617.63, 124.91 562.23, 93.24 705.90, 61.57 739.64, 29.89 587.53, -7.55 589.31, -44.98 643.83, -82.42 726.01, -103.43 676.92, -124.43 700.44, -145.43 603.98, -182.70 553.13, -257.24 653.77, -300.35 588.33, -321.90 567.47, -342.46 549.48, -363.01 654.41, -383.57 694.84, -433.36 577.45, -483.15 623.12, -532.94 679.78, -557.28 573.81, -605.95 586.75, -631.80 704.04, -657.64 752.60, -683.48 753.38, -711.75 625.74, -768.29 742.68, -911.74 743.44, -937.92 649.59, -964.10 715.00, -990.28 609.89, -1089.01 716.06, -1138.38 686.33, -1203.41 745.95, -1235.93 755.68, -1263.04 626.40, -1290.15 577.61, -1317.26 543.92, -1342.74 553.95, -1368.23 675.79, -1393.71 692.75, -1419.73 715.40, -1445.76 536.53, -1471.78 526.48, -1500.31 695.29, -1557.39 703.06, -1601.51 699.74, -1689.77 599.24, -1778.97 598.25, -1922.16 584.80, -1949.38 670.35, -2003.83 703.64, -2035.42 626.89, -2067.01 571.29, -2098.61 691.37, -2138.58 623.11, -2158.57 522.64, -2201.07 643.83, -2243.57 696.65, -2286.08 599.58, -2320.46 660.74, -2354.84 573.16, -2389.22 540.85, -2423.58 599.99, -2457.93 594.51, -2492.29 653.63, -2635.04 533.07, -2667.07 567.86, -2699.11 621.04, -2731.14 715.87, -2810.23 577.88, -2902.75 547.31, -3005.21 550.03, -3038.91 666.48, -3055.75 627.29, -3111.85 627.06, -3139.90 614.40, -3186.39 752.90, -3279.37 620.56, -3328.84 595.85, -3427.77 720.85, -3471.42 591.02, -3493.25 763.63, -3587.95 643.68, -3635.30 651.18, -3725.48 574.18, -3763.73 539.84, -3782.86 650.71, -3890.77 626.72, -3908.24 586.59, -3925.71 701.51, -3943.18 542.25, -3969.58 651.43, -4022.37 610.48, -4055.90 685.92, -4122.95 518.40, -4195.65 561.64, -4257.98 591.72, -4289.14 582.51, -4327.27 655.74, -4365.39 654.41, -4403.51 522.12, -4484.86 658.47, -4525.54 590.38, -4667.21 575.98, -4701.25 479.61, -4769.35 658.55, -4822.88 610.21, -4953.38 582.98, -5004.70 676.07, -5026.66 547.63, -5048.62 605.30, -5070.59 665.25, -5113.71 612.86, -5135.27 692.78, -5162.20 724.52, -5216.07 742.28, -5246.37 689.27, -5276.68 615.61, -5306.99 592.84, -5365.67 577.65, -5395.02 688.99, -5473.14 555.91, -5512.21 724.35, -5553.47 629.14, -5594.74 651.09, -5636.01 661.59, -5678.49 645.79, -5720.98 696.37, -5763.46 647.38, -5810.70 641.65, -5905.18 569.91, -5992.75 635.32, -6012.49 584.88, -6051.96 689.88, -6130.68 637.23, -6182.60 650.27, -6208.55 728.78, -6269.49 685.35, -6297.79 538.60, -6326.09 664.00, -6354.39 603.23, -6401.24 664.09, -6494.94 576.83, -6524.99 754.34, -6585.07 582.07, -6604.23 619.22, -6642.55 669.72, -6699.09 623.59, -6727.36 617.22, -6870.24 572.52, -6910.27 590.68, -6950.30 566.97, -6990.32 630.59, -7039.06 599.12, -7087.79 597.79, -7136.53 702.99, -7234.58 695.41, -7259.91 646.68, -7310.57 698.66, -7328.74 613.10, -7346.90 692.18, -7365.07 709.15, -7440.39 709.15, -7478.05 698.18, -7517.44 734.82, -7556.83 625.55, -7596.22 718.98, -7729.88 684.10, -7773.11 649.71, -7859.57 532.89, -7888.15 561.54, -7916.73 584.06, -7945.31 532.40, -7996.20 622.29, -8021.65 662.98, -8114.87 504.37, -8202.68 726.63, -8246.59 519.06, -8371.72 557.25, -8397.43 626.31, -8423.13 587.01, -8448.84 581.28, -8478.94 705.16, -8509.04 623.13, -8539.14 615.07, -8678.69 704.68, -8734.32 598.98, -8803.60 614.41, -8838.24 807.08, -8864.18 728.85, -8916.06 806.92, -9064.02 675.17, -9108.41 734.03, -9197.19 756.03, -9288.23 641.29, -9329.22 646.03, -9411.21 800.34, -9459.50 664.37, -9507.80 671.49, -9556.10 647.82, -9610.45 650.34, -9648.08 750.80, -9723.34 677.60, -9767.93 761.26, -9857.12 690.45, -9905.86 643.16, -9954.61 815.81, -10003.35 805.19, -10049.56 787.67, -10095.77 682.59, -10141.98 664.28, -10183.94 688.47, -10225.89 737.35, -10267.84 751.51, -10397.82 619.79, -10417.89 665.29, -10458.03 814.42, -10493.93 804.26, -10565.72 761.08, -10624.67 822.75, -10654.14 628.04, -10681.30 764.21, -10708.46 690.22, -10735.62 763.67, -10807.04 706.95, -10826.48 795.34, -10865.38 715.72, -10921.85 713.17, -10950.09 631.27, -11040.54 670.52, -11089.87 732.93, -11139.20 778.33, -11188.53 689.70, -11252.87 704.06, -11285.04 589.09, -11328.95 647.90, -11416.78 587.10, -11556.59 692.91, -11695.60 633.80, -11637.62 1091.43))
    #POLYGON ((-11163.62 -630.21, -11135.22 -615.38, -11118.02 -590.19, -11100.81 -630.81, -11054.21 -650.31, -11007.61 -674.33, -10961.01 -634.89, -10917.10 -636.45, -10829.27 -645.72, -10764.93 -640.98, -10732.76 -574.63, -10584.77 -567.07, -10554.62 -601.84, -10524.47 -615.51, -10494.32 -594.37, -10437.85 -565.84, -10409.61 -580.52, -10390.16 -582.78, -10351.27 -537.51, -10327.46 -574.44, -10303.66 -585.52, -10279.85 -552.50, -10198.37 -602.04, -10139.43 -586.22, -10109.95 -549.37, -10074.06 -530.44, -10002.26 -544.43, -9982.19 -544.14, -9942.05 -579.09, -9898.72 -567.84, -9855.40 -607.22, -9812.07 -550.34, -9686.21 -614.43, -9547.58 -596.15, -9401.35 -543.56, -9356.75 -568.70, -9267.57 -555.09, -9229.94 -585.97, -9154.68 -600.49, -9136.56 -616.94, -9118.44 -572.44, -9100.32 -578.37, -8955.44 -577.39, -8914.45 -534.82, -8832.46 -512.48, -8802.11 -535.92, -8771.76 -561.09, -8741.42 -567.44, -8697.03 -541.24, -8608.25 -550.54, -8558.93 -592.48, -8509.61 -587.99, -8460.29 -558.45, -8434.35 -574.43, -8382.46 -565.06, -8313.19 -591.39, -8278.55 -598.06, -8260.01 -604.50, -8241.46 -593.40, -8222.92 -604.44, -8176.40 -617.99, -8129.89 -643.14, -8083.37 -669.37, -7993.07 -680.21, -7915.95 -690.90, -7874.24 -712.69, -7832.53 -673.63, -7790.82 -643.17, -7703.00 -701.17, -7659.09 -709.04, -7628.02 -705.69, -7596.95 -655.59, -7565.88 -678.28, -7514.99 -675.08, -7489.54 -657.41, -7403.80 -684.04, -7360.57 -678.38, -7274.11 -646.91, -7229.56 -661.14, -7185.00 -695.05, -7140.45 -650.13, -7022.28 -667.06, -6946.96 -663.04, -6909.30 -683.17, -6854.80 -683.94, -6829.47 -648.51, -6778.81 -682.86, -6746.12 -679.92, -6713.44 -680.04, -6680.76 -614.82, -6534.55 -633.47, -6414.47 -642.58, -6366.85 -588.71, -6319.22 -614.40, -6271.59 -596.97, -6215.05 -671.99, -6186.78 -633.20, -6167.62 -652.15, -6129.30 -624.93, -6099.26 -649.18, -6039.17 -608.75, -5992.32 -631.45, -5898.62 -669.27, -5813.72 -692.28, -5793.41 -700.16, -5773.10 -658.35, -5752.78 -677.58, -5700.87 -688.82, -5674.91 -601.79, -5648.67 -610.90, -5622.43 -664.81, -5596.19 -615.55, -5576.46 -666.94, -5536.98 -653.64, -5507.79 -653.30, -5478.60 -634.45, -5449.41 -606.72, -5402.17 -651.70, -5307.69 -598.79, -5180.24 -662.99, -5056.44 -687.00, -4978.31 -676.99, -4939.25 -659.75, -4880.56 -672.95, -4851.22 -630.18, -4760.30 -606.69, -4733.37 -651.57, -4679.50 -634.29, -4636.38 -701.10, -4614.81 -702.03, -4548.93 -668.22, -4531.82 -739.40, -4514.72 -740.21, -4497.61 -692.36, -4454.11 -717.86, -4410.61 -762.36, -4367.11 -748.93, -4349.27 -741.41, -4331.42 -761.27, -4313.58 -703.11, -4279.53 -752.58, -4211.44 -753.98, -4164.22 -738.08, -4116.99 -687.28, -4069.77 -708.01, -3988.42 -760.40, -3947.74 -754.95, -3833.37 -721.14, -3771.04 -692.80, -3739.88 -724.65, -3715.64 -688.63, -3691.41 -708.82, -3667.18 -675.99, -3633.65 -715.98, -3566.60 -668.41, -3540.20 -661.99, -3487.41 -680.23, -3435.00 -686.95, -3399.03 -669.20, -3363.06 -642.96, -3327.09 -657.00, -3288.83 -701.46, -3269.71 -642.06, -3239.65 -678.37, -3209.59 -634.67, -3179.53 -597.49, -3084.83 -646.90, -3037.48 -609.03, -2993.83 -628.00, -2972.00 -608.37, -2922.53 -658.24, -2823.60 -639.83, -2777.11 -613.03, -2684.13 -665.09, -2628.03 -686.32, -2599.98 -669.72, -2566.29 -671.20, -2549.44 -640.70, -2515.29 -717.79, -2481.14 -714.99, -2446.98 -679.12, -2416.14 -673.34, -2385.30 -690.70, -2354.46 -638.45, -2328.10 -668.74, -2301.73 -632.03, -2275.37 -683.83, -2179.27 -652.67, -2131.68 -683.46, -2084.10 -735.91, -2036.52 -692.11, -1933.45 -650.81, -1830.31 -707.76, -1702.80 -718.07, -1662.82 -747.44, -1642.84 -722.72, -1548.06 -639.62, -1520.83 -682.76, -1466.39 -632.48, -1418.66 -678.03, -1370.93 -660.02, -1323.20 -673.97, -1293.47 -665.98, -1263.73 -720.35, -1234.00 -714.83, -1189.87 -659.87, -1101.61 -657.18, -1073.08 -682.36, -1016.01 -686.28, -937.94 -660.24, -861.49 -674.13, -780.16 -641.48, -715.13 -648.33, -682.61 -629.74, -583.88 -623.78, -534.51 -592.83, -455.97 -615.35, -408.15 -639.92, -360.34 -597.42, -312.52 -609.85, -284.25 -629.30, -227.71 -622.48, -150.18 -631.11, -125.84 -664.93, -77.17 -643.63, 72.20 -672.91, 133.87 -653.20, 176.98 -675.27, 198.53 -685.86, 235.80 -674.29, 310.34 -670.87, 373.35 -690.21, 485.66 -612.70, 580.68 -632.43, 672.08 -625.77, 740.97 -631.05, 775.41 -642.91, 823.56 -603.35, 871.70 -604.23, 919.84 -626.28, 977.73 -584.14, 1026.27 -599.43, 1123.35 -643.78, 1154.47 -666.50, 1185.58 -626.14, 1216.69 -652.32, 1279.75 -624.94, 1311.28 -637.45, 1328.89 -601.82, 1346.51 -626.23, 1364.13 -641.59, 1462.69 -650.76, 1555.11 -683.67, 1601.32 -641.19, 1721.64 -677.96, 1751.72 -735.03, 1781.81 -741.39, 1811.89 -673.82, 1855.40 -719.04, 1942.41 -692.55, 1990.72 -679.92, 2014.87 -679.43, 2109.33 -716.51, 2203.72 -726.73, 2236.64 -762.16, 2302.47 -705.76, 2330.36 -743.45, 2358.25 -711.34, 2386.14 -701.63, 2409.60 -695.04, 2456.52 -702.54, 2547.10 -728.88, 2592.39 -747.06, 2617.64 -752.49, 2668.15 -734.05, 2726.39 -752.99, 2755.52 -741.50, 2831.00 -694.36, 2866.29 -715.23, 2936.88 -721.21, 3008.44 -726.47, 3053.79 -752.38, 3076.47 -740.83, 3178.84 -707.07, 3255.99 -731.89, 3294.57 -751.98, 3333.62 -730.13, 3411.71 -714.21, 3428.97 -714.27, 3463.50 -693.79, 3508.21 -688.94, 3552.91 -703.41, 3597.62 -667.43, 3655.92 -731.35, 3685.07 -705.83, 3719.64 -753.92, 3736.92 -711.27, 3764.92 -750.44, 3792.91 -764.43, 3820.91 -715.37, 3961.09 -738.41, 4003.70 -747.32, 4046.32 -696.82, 4088.93 -744.09, 4135.43 -724.71, 4181.93 -728.73, 4228.44 -725.94, 4274.51 -764.15, 4366.65 -760.90, 4387.45 -746.94, 4429.05 -747.15, 4469.70 -724.93, 4551.00 -728.29, 4594.22 -724.90, 4637.45 -701.99, 4680.67 -729.87, 4721.14 -703.70, 4802.06 -719.59, 4836.82 -721.62, 4854.19 -688.95, 4885.43 -684.30, 4916.66 -695.69, 4947.89 -716.77, 4970.13 -712.77, 4992.37 -711.87, 5014.61 -718.46, 5062.76 -646.83, 5159.06 -713.27, 5237.31 -695.12, 5276.43 -690.65, 5295.75 -727.87, 5315.07 -697.85, 5334.39 -701.86, 5437.03 -717.25, 5473.59 -719.84, 5491.87 -686.21, 5554.16 -708.05, 5585.31 -717.71, 5660.02 -694.16, 5686.98 -704.74, 5740.92 -670.96, 5814.49 -649.42, 5857.18 -707.67, 5899.87 -713.13, 5942.56 -695.05, 6007.76 -624.15, 6046.71 -682.43, 6124.61 -609.16, 6216.93 -659.99, 6263.09 -630.89, 6326.25 -595.10, 6397.21 -637.61, 6432.68 -647.49, 6486.52 -629.31, 6513.43 -616.36, 6631.86 -643.59, 6737.27 -658.27, 6764.89 -645.85, 6792.51 -616.51, 6820.12 -636.16, 6890.62 -662.98, 6925.87 -648.58, 6983.00 -586.82, 7066.36 -564.95, 7100.56 -627.01, 7117.66 -589.10, 7158.46 -553.18, 7240.05 -579.10, 7261.12 -544.32, 7282.20 -542.40, 7303.27 -527.67, 7329.35 -529.51, 7355.44 -512.31, 7381.52 -510.92, 7423.51 -507.38, 7465.49 -518.85, 7507.48 -495.47, 7603.06 -479.83, 7650.84 -466.58, 7690.57 -455.32, 7730.30 -462.49, 7770.02 -475.09, 7874.53 -462.69, 7911.57 -428.74, 7948.60 -451.27, 7985.64 -469.70, 8042.13 -429.00, 8070.38 -433.53, 8169.32 -442.27, 8218.79 -498.49, 8283.02 -485.51, 8315.14 -433.20, 8339.52 -485.69, 8388.30 -468.32, 8500.90 -478.77, 8521.47 -424.34, 8542.04 -474.07, 8562.61 -487.16, 8590.64 -518.89, 8618.67 -465.43, 8646.70 -477.05, 8691.80 -487.18, 8714.35 -466.76, 8822.26 -458.24, 8868.41 -504.30, 8960.70 -503.85, 8980.40 -455.98, 9019.79 -483.77, 9074.50 -461.57, 9137.69 -466.22, 9169.28 -492.08, 9255.97 -499.04, 9299.32 -485.81, 9420.96 -511.34, 9450.90 -529.91, 9480.85 -518.94, 9510.79 -515.63, 9610.95 -560.68, 9680.33 -576.25, 9812.26 -600.71, 9754.20 -671.38, 9645.64 -670.78, 9610.95 -725.83, 9577.56 -674.08, 9544.17 -718.94, 9510.79 -708.49, 9420.96 -650.14, 9380.41 -675.98, 9339.87 -635.19, 9299.32 -673.58, 9212.63 -642.63, 9169.28 -642.29, 9106.09 -654.07, 9074.50 -647.84, 9056.26 -610.44, 9038.03 -596.06, 9019.79 -645.59, 9000.10 -614.75, 8960.70 -608.25, 8914.55 -631.21, 8822.26 -661.82, 8786.29 -657.16, 8750.32 -623.83, 8714.35 -661.09, 8669.25 -612.44, 8646.70 -611.18, 8562.61 -616.81, 8500.90 -648.84, 8463.37 -598.40, 8425.83 -656.66, 8388.30 -623.67, 8363.91 -589.92, 8315.14 -592.83, 8250.91 -622.17, 8218.79 -618.26, 8119.85 -582.04, 8070.38 -573.76, 8013.89 -585.75, 7985.64 -582.37, 7874.53 -616.68, 7839.70 -566.53, 7804.86 -598.00, 7770.02 -588.12, 7650.84 -596.70, 7555.27 -606.78, 7507.48 -672.98, 7381.52 -682.30, 7303.27 -712.04, 7240.05 -744.71, 7199.26 -689.79, 7117.66 -755.94, 7083.46 -752.20, 7066.36 -721.80, 7038.57 -763.52, 7010.79 -776.38, 6983.00 -794.42, 6963.96 -730.31, 6944.91 -783.89, 6925.87 -791.56, 6855.37 -772.27, 6820.12 -769.96, 6737.27 -755.39, 6702.14 -752.22, 6667.00 -777.10, 6631.86 -803.86, 6592.39 -794.43, 6552.91 -769.65, 6513.43 -754.73, 6459.60 -789.30, 6432.68 -820.38, 6361.73 -767.94, 6326.25 -761.10, 6305.19 -758.99, 6284.14 -759.61, 6263.09 -785.97, 6170.77 -772.81, 6124.61 -755.01, 6085.66 -799.81, 6007.76 -824.98, 5986.03 -784.35, 5964.29 -793.25, 5942.56 -819.45, 5814.49 -857.55, 5789.97 -832.08, 5765.44 -829.42, 5740.92 -853.50, 5713.95 -863.33, 5660.02 -860.64, 5635.12 -848.31, 5610.21 -815.64, 5585.31 -852.90, 5523.02 -881.64, 5491.87 -841.14, 5455.31 -830.20, 5437.03 -850.84, 5402.82 -834.59, 5368.60 -818.94, 5334.39 -862.60, 5276.43 -840.03, 5198.18 -820.06, 5159.06 -820.46, 5110.91 -796.74, 5014.61 -860.22, 4947.89 -870.89, 4854.19 -819.06, 4819.44 -811.78, 4802.06 -860.61, 4761.60 -821.93, 4680.67 -896.57, 4551.00 -893.25, 4510.35 -929.70, 4429.05 -891.82, 4408.25 -911.29, 4366.65 -950.94, 4320.58 -894.47, 4228.44 -855.24, 4088.93 -871.84, 3961.09 -875.97, 3914.36 -894.36, 3867.63 -864.92, 3820.91 -880.86, 3736.92 -909.83, 3702.35 -887.88, 3685.07 -874.27, 3626.77 -868.20, 3597.62 -873.67, 3463.50 -838.41, 3446.24 -882.82, 3411.71 -844.33, 3372.67 -846.47, 3294.57 -876.90, 3217.42 -879.86, 3178.84 -887.62, 3144.71 -880.79, 3110.59 -839.91, 3076.47 -879.22, 3031.11 -869.56, 3008.44 -937.69, 2984.59 -851.90, 2960.73 -865.26, 2936.88 -882.02, 2901.59 -830.23, 2831.00 -896.64, 2805.84 -857.50, 2780.68 -845.12, 2755.52 -874.46, 2697.27 -936.17, 2668.15 -912.93, 2642.90 -898.58, 2592.39 -862.30, 2501.81 -856.63, 2456.52 -852.63, 2433.06 -834.58, 2386.14 -865.53, 2302.47 -848.03, 2269.56 -875.29, 2203.72 -874.12, 2172.26 -895.36, 2140.79 -877.19, 2109.33 -863.89, 2077.84 -863.29, 2046.36 -796.86, 2014.87 -832.82, 1966.56 -839.86, 1942.41 -836.49, 1898.91 -813.14, 1811.89 -911.81, 1721.64 -831.63, 1681.53 -854.93, 1641.42 -853.98, 1601.32 -831.34, 1508.90 -815.75, 1462.69 -790.54, 1429.84 -774.43, 1396.98 -807.08, 1364.13 -756.46, 1311.28 -827.77, 1248.22 -787.23, 1216.69 -795.76, 1123.35 -733.32, 1074.81 -729.89, 977.73 -757.04, 958.43 -784.20, 939.14 -754.18, 919.84 -773.27, 775.41 -777.88, 706.52 -752.09, 672.08 -817.93, 641.61 -822.04, 611.15 -815.88, 580.68 -837.59, 549.01 -774.94, 517.34 -759.64, 485.66 -808.92, 448.23 -824.96, 410.79 -803.49, 373.35 -787.36, 352.35 -797.48, 331.34 -793.02, 310.34 -825.24, 273.07 -819.80, 198.53 -800.57, 155.42 -814.72, 133.87 -836.52, 113.31 -842.59, 92.76 -811.56, 72.20 -800.22, 22.41 -825.54, -27.38 -804.38, -77.17 -788.33, -101.51 -833.12, -150.18 -809.46, -176.02 -754.02, -201.87 -735.36, -227.71 -752.72, -255.98 -784.15, -312.52 -761.64, -455.97 -753.97, -482.15 -774.50, -508.33 -764.08, -534.51 -794.79, -633.24 -735.12, -682.61 -762.83, -747.64 -748.50, -780.16 -753.74, -807.27 -807.75, -834.38 -812.02, -861.49 -839.01, -886.97 -826.47, -912.46 -802.54, -937.94 -792.65, -963.96 -794.40, -989.99 -836.80, -1016.01 -865.82, -1044.54 -814.38, -1101.61 -799.43, -1145.74 -789.85, -1234.00 -839.87, -1323.20 -846.81, -1466.39 -835.15, -1493.61 -795.82, -1548.06 -798.22, -1579.65 -838.14, -1611.24 -846.86, -1642.84 -826.58, -1682.81 -833.75, -1702.80 -876.34, -1745.30 -826.28, -1787.80 -797.10, -1830.31 -838.59, -1864.69 -826.21, -1899.07 -836.52, -1933.45 -850.02, -1967.81 -833.71, -2002.16 -830.81, -2036.52 -817.78, -2179.27 -872.38, -2211.30 -848.86, -2243.33 -813.50, -2275.37 -792.21, -2354.46 -840.91, -2446.98 -848.56, -2549.44 -857.64, -2583.14 -799.03, -2599.98 -822.33, -2656.08 -804.45, -2684.13 -803.48, -2730.62 -762.09, -2823.60 -802.91, -2873.07 -791.15, -2972.00 -753.51, -3015.65 -798.18, -3037.48 -740.96, -3132.18 -782.55, -3179.53 -795.74, -3269.71 -846.23, -3307.96 -851.51, -3327.09 -808.18, -3435.00 -818.03, -3452.47 -816.70, -3469.94 -785.60, -3487.41 -859.30, -3513.81 -811.91, -3566.60 -845.59, -3600.13 -818.88, -3667.18 -876.82, -3739.88 -869.37, -3802.21 -857.56, -3833.37 -865.98, -3871.50 -847.56, -3909.62 -834.17, -3947.74 -888.38, -4029.09 -840.93, -4069.77 -876.66, -4211.44 -873.01, -4245.48 -907.86, -4313.58 -849.64, -4367.11 -854.26, -4497.61 -857.86, -4548.93 -824.15, -4570.89 -849.28, -4592.85 -844.81, -4614.81 -809.40, -4657.94 -840.37, -4679.50 -796.01, -4706.43 -770.24, -4760.30 -763.38, -4790.60 -765.38, -4820.91 -786.29, -4851.22 -812.62, -4909.90 -809.92, -4939.25 -782.50, -5017.37 -833.96, -5056.44 -774.00, -5097.70 -794.72, -5138.97 -794.53, -5180.24 -781.28, -5222.72 -775.99, -5265.21 -760.81, -5307.69 -800.21, -5354.93 -779.69, -5449.41 -816.43, -5536.98 -797.12, -5556.72 -814.55, -5596.19 -771.34, -5674.91 -800.51, -5726.83 -791.98, -5752.78 -780.17, -5813.72 -802.71, -5842.02 -844.45, -5870.32 -804.66, -5898.62 -824.54, -5945.47 -795.92, -6039.17 -824.19, -6069.21 -756.80, -6129.30 -813.46, -6148.46 -782.03, -6186.78 -785.93, -6243.32 -811.11, -6271.59 -802.61, -6414.47 -814.80, -6454.50 -822.34, -6494.53 -811.47, -6534.55 -788.09, -6583.29 -801.45, -6632.02 -791.97, -6680.76 -770.62, -6778.81 -779.10, -6804.14 -805.98, -6854.80 -791.93, -6872.97 -821.03, -6891.13 -792.40, -6909.30 -789.16, -6984.62 -779.37, -7022.28 -779.93, -7061.67 -752.52, -7101.06 -791.04, -7140.45 -778.51, -7274.11 -801.59, -7317.34 -813.76, -7403.80 -863.68, -7432.38 -868.56, -7460.96 -860.14, -7489.54 -861.37, -7540.43 -825.04, -7565.88 -825.50, -7659.09 -882.09, -7746.91 -783.51, -7790.82 -858.50, -7915.95 -851.57, -7941.66 -808.19, -7967.36 -812.54, -7993.07 -821.49, -8023.17 -779.84, -8053.27 -798.59, -8083.37 -802.94, -8222.92 -770.52, -8278.55 -779.20, -8347.83 -769.85, -8382.46 -698.06, -8408.41 -723.02, -8460.29 -686.72, -8608.25 -725.70, -8652.64 -701.95, -8741.42 -696.38, -8832.46 -759.67, -8873.45 -745.16, -8955.44 -688.37, -9003.73 -729.93, -9052.03 -750.21, -9100.32 -743.66, -9154.68 -763.56, -9192.31 -710.01, -9267.57 -741.56, -9312.16 -694.26, -9401.35 -734.38, -9450.09 -743.60, -9498.83 -678.55, -9547.58 -697.63, -9593.79 -698.16, -9640.00 -744.36, -9686.21 -758.13, -9728.17 -752.88, -9770.12 -734.86, -9812.07 -731.35, -9942.05 -755.60, -9962.12 -740.50, -10002.26 -680.87, -10038.16 -674.08, -10109.95 -693.81, -10168.90 -676.94, -10198.37 -768.10, -10225.53 -720.65, -10252.69 -744.01, -10279.85 -706.24, -10351.27 -727.20, -10370.71 -699.92, -10409.61 -731.22, -10466.08 -725.15, -10494.32 -758.90, -10584.77 -751.18, -10634.10 -731.61, -10683.43 -711.21, -10732.76 -768.32, -10797.10 -763.17, -10829.27 -791.05, -10873.18 -782.24, -10961.01 -819.48, -11100.81 -775.06, -11182.35 -791.80, -11163.62 -630.21))

    op_st = ['Intersects', 'Touches', 'Disjoint', 'Contains', 'Within']
    op_st = ['Intersects']

    print('MR X MP -> P : N Tests: ' + str(NTESTS))
    print('Op;mET (sec);MET (sec);mSET (sec);MSET (sec);AVGET %;NV;NIT;MPTT')

    k = 0
    while k < len(op_st):
        for el in tests_r:
            str = op_st[k] + ';'
            for e in el[k]:
                str += e + ';'

            print(str)

        k += 1

    sys.exit()

begin_exec_time = time.time()

ccw = True
p_wkt = str(sys.argv[1])
q_wkt = str(sys.argv[2])

mpoint = str(sys.argv[3])

t0 = 1000
t1 = 2000

# 2. create objects

p = loads(p_wkt)
q = loads(q_wkt)

# 2.1 get region moving segments from observations

reg_m_segs = get_moving_segs_from_observations(p, q, t0, t1)

if reg_m_segs == None:
    print_error(err_code, err_msg)

# 2.3 create the moving point 

mpoint = create_moving_point([mpoint])

# 2.3 get states w.r.t the region

initial_state, final_state = get_states(p, q, mpoint)

# 2.4 get the intersections betwen the two objects

if operation == Operation.Intersects.value \
or operation == Operation.Disjoint.value \
or operation == Operation.Within.value \
or operation == Operation.Touches.value \
or operation == Operation.Contains.value:
    get_mr_mp_intersections(reg_m_segs, mpoint, initial_state, final_state, operation, p_linear_traj, ccw)
else:
    print_error(-1, 'Unsupported operation : Equals!')
