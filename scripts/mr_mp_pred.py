#-------------------------------------------------------------------
# Imports.
#-------------------------------------------------------------------
import collections
import os
import sys
import re
import json
import random
import numpy as np
import time
import math
import enum

#sys.float_info

from sympy import symbols, Eq, solve, re, im, S, Interval as SpyInterval
from sympy import Symbol
from sympy.solvers import solveset
from geomet import wkt

#from shapely.geometry import Point as shPoint
from shapely.geometry.polygon import Polygon as shPolygon
from shapely.geometry import MultiLineString, LineString

import numpy as np
from shapely.geometry import Point, Polygon, LineString, MultiPolygon
from shapely.geometry import GeometryCollection, mapping

import shapely.wkt
from shapely.wkt import dumps, loads
import math
from MSeg import MSeg
import sys
import Seg

import math
from math import atan

from Utils import distance
from sympy import S 

# import complex math module
import cmath

M_PI = 3.14159265358979323846
M_PI_OVER_2 = M_PI / 2

#class Predicate(enum.Enum): 
class Operation(enum.Enum): 
    Intersects = 1
    Touches = 2
    Equals = 3
    Disjoint = 4
    Contains = 5
    Within = 6
    Crosses = 7
    Overlaps = 8

class STOperation(enum.Enum): 
    Intersection = 9
    #Intersection2 = 10

class State(enum.Enum): 
    Intersect = 1
    Touch = 2
    Disjoint = 3
    Inside = 4

#-------------------------------------------------------------------
# Classes.
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

"""
class MPU2:

    def __init__(self, c, i):
        self.c = c
        self.i = i

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
"""

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

        """
        n = len(self.units)
        i, t = self.get_unit_and_time(t)

        if i < 0 or i > n - 1:
            return None, None, None, None

        return self.units[i].at(t)
        """

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

        """
        n = len(self.units)
        i, t = self.get_unit_and_time(t)

        if i < 0 or i > n - 1:
            return None

        return self.units[i].wkt_at(t)
        """

    """
    def get_unit_and_time(self, t):
        i = -1
        n = len(self.units)

        if t == 1:
            i = n - 1
        else:
            t = t * n
            t, i = math.modf(t)

        return int(i), t
    """

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
# Usage examples.
#-------------------------------------------------------------------

"""
	Moving region moving point predicates

	MS*MP Operations:
	Predicates:
		Equals
		Disjoint
		Touches
		Contains
		Covers
		Intersects
		Within (Inside)
		Crosses
		Overlaps
		
Equals 		The Geometries are topologically equal
Disjoint 	The Geometries have no point in common
Intersects 	The Geometries have at least one point in common (the inverse of Disjoint)
Touches 	The Geometries have at least one boundary point in common, but no interior points
Crosses 	The Geometries share some but not all interior points, and the dimension of the intersection is less than that of at least one of the Geometries
Overlaps 	The Geometries share some but not all points in common, and the intersection has the same dimension as the Geometries themselves
Within 		Geometry A lies in the interior of Geometry B
Contains 	Geometry B lies in the interior of Geometry A (the inverse of Within)

			Interior					Boundary
Point		Point						Empty
Line		Points left when the		End Points
			boundary is removed 				

MS*MP			
Intersects
Touches		The point intersects the boundary of the line
Equals		A MS and a MP are not equal
Disjoint	
Crosses		(NA)
Overlaps	(NA)
Contains	
Within		

Intersects(MS, MP)
Intersects(MP, MS)
Touches(MS, MP)
Touches(MP, MS)
Intersects 	= not(Disjoint)
Equals 		= False by def.
Crosses		(NA)
Overlaps	(NA)
Contains	Use (2). Contains(MS, MP)
Within		Use (2). Within(MP, MS)

Touches (1):
	solve system of linear equations
	Ax - Cx = 0
	Ay - Cy = 0

	Bx - Cx = 0
	By - Cy = 0
	
Intersects (2)

Disjoint	The boundaries and interiors do not intersect.
Equals		The features have the same boundary and the same interior.
Touches		The boundaries may intersect or one boundary may intersect the other interior.
			The interiors do not touch.
Crosses		The interiors intersect and the base's interior intersects the candidate's exterior.
			In the case of line/line, the intersection of the interiors forms a point.
Overlaps	The interiors intersect, but neither feature is contained by the other, nor are the features equal.
Contains	The interiors intersect and no part of the candidate's interior or boundary intersects the base's exterior. It is possible for the boundaries to intersect.
			Inverse of WITHIN.
Within		The interiors intersect and no part of the base's interior or boundary intersects the candidate's exterior. It is possible for the boundaries to intersect.
	
Predicates between MS / MP

check at every instant ti?
compute the geometry created by the evolution of the MOs during I?

Touches:
	solve system of linear equations
	Ax - Cx = 0
	Ay - Cy = 0

	Bx - Cx = 0
	By - Cy = 0

intersects
touches
equals
disjoint
crosses
overlaps
contains
within

"""

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
#tprecision = '.3f'
operation = 1
eps = 0.000001				# Temporal eps.
err_msg = None
err_code = 0
initial_state = None
p_linear_traj = False
begin_exec_time = 0
precision_0 = '.0f'

#-------------------------------------------------------------------
# Check if the given points are collinear.
#-------------------------------------------------------------------
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
# Get paremeters.
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

    #print(sys.argv[4], sys.argv[5], sys.argv[6], sys.argv[7])

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
# Create a moving segment.
#-------------------------------------------------------------------
def create_moving_segment(units, pass_through_control_points):
    ms = MovingSegment()

    for u in units:
        c0 = CCurve()
        c1 = CCurve()

        u = u.split("#")
        t = 0.5

        if len(u) != 3:
            print_error(-1, 'create_moving_segment > Invalid unit data! ' + u)
            #print(u)
            #print("ERR: Invalid unit data.")
            #sys.exit()

        cp0 = u[0].split(",")
        cp1 = u[1].split(",")
        intervals = u[2].split(":")

        if len(cp0) != len(cp1):
            print_error(-1, 'create_moving_segment > Different number of control points! ' + cp0 + ' : ' + cp1)
            #print(cp0)
            #print(cp1)
            #print("ERR: Different number of control points.")
            #sys.exit()

        if (len(cp0) - 6) % 2 != 0 or (len(cp1) - 6) % 2 != 0:
            print_error(-1, 'create_moving_segment > Invalid control points data! ' + cp0 + ' : ' + cp1)
            #print(cp0)
            #print(cp1)
            #print("ERR: Invalid control points data.")
            #sys.exit()

        m = ((len(cp0) - 6) / 4) + 1

        if (len(intervals)) - 1 != m:
            print_error(-1, 'create_moving_segment > Invalid interval data! ' + str(len(intervals) - 1) + ' : ' + str(m))
            #print(len(intervals) - 1)
            #print(m)
            #print("ERR: Invalid interval data.")
            #sys.exit()

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

            #print(p0.wkt, p1.wkt, p2.wkt)

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

                #if dir(p0, p2, p1) == 0:
                #    c = QuadBezierCurve(p0, Point(x, y), p2, True)
                #else:
                c = QuadBezierCurve(p0, Point(x, y), p2)
            else:
                c = QuadBezierCurve(p0, p1, p2)

            c1.add_curve(c, i)
            #print(c.degenerated_to_linear)

            idx += step
            k += 1

        i = intervals[k].split(",")
        i = Interval(float(i[0]), float(i[1]), True, False)
        u = MSU(c0, c1, i)

        ms.add_unit(u)

    return ms

#-------------------------------------------------------------------
# Create a moving point.
#-------------------------------------------------------------------
def create_moving_point(units):
    global p_linear_traj
    global pass_through_control_points

    mp = MovingPoint()

    for u in units:
        u = u.split("#")

        """
        if len(u) != 3:
            print(u)
            print("ERR: Invalid unit data.")
            sys.exit()

        cp0 = u[0].split(",")
        cp1 = u[1].split(",")
        intervals = u[2].split(":")

        if len(cp0) != len(cp1):
            print(cp0)
            print(cp1)
            print("ERR: different number of control points.")
            sys.exit()

        if len(cp0) < 2 or len(cp0) > 3:
            print(cp0)
            print(cp1)
            print("ERR: invalid number of control points.")
            sys.exit()

        if len(intervals) != 1:
            print(len(intervals))
            print("ERR: invalid interval.")
            sys.exit()

        i = intervals[0].split(",")
        i = Interval(float(i[0]), float(i[1]), True, False)
        """

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
# Collect n samples for viz.
#-------------------------------------------------------------------
def get_samples_for_viz(ms, mp, i, n_samples, s):
    n = (n_samples - 1)
    k = 0
    dt = i.y - i.x
    eq = False

    for j in range(0, n_samples):
        t = i.x + dt * (float(j) / n)

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    print(ms.wkt_at(t))
                    print(mp.wkt_at(t))
                    print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    print(ms.wkt_at(s[k]))
                    print(mp.wkt_at(s[k]))
                    print(1)
                    k += 1

                    #if s[k] == t:
                    eq = True

        if not eq:
            print(ms.wkt_at(t))
            print(mp.wkt_at(t))
            print(0)
        else:
            eq = False

def get_mline(MS, t):
    lines = []

    for ms in MS:
        lines += [(ms.obj_at(t))]

    #return GeometryCollection(lines)
    return MultiLineString(lines)

def get_lines(MS, t):
    for ms in MS:
        print(ms.obj_at(t).wkt + ';')

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
                    """
                    if J < N and t >= T[J]:
                        t = T[J]
                        J += 1

                    mline = get_mline(MS, t)
                    """
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
                    """
                    if J < N and t >= T[J]:
                        t = T[J]
                        J += 1

                    mline = get_mline(MS, t)
                    """
                    print(mline.wkt)
                    print(mp.wkt_at(t))

                    if flag:
                        print(out)
                    else:
                        print(1)

                    #print(1)
                    k += 1

                    eq = True

        if not eq:
            """
            out = '0'

            if J < N and t >= T[J]:
                t = T[J]
                out = '1'
                J += 1

            mline = get_mline(MS, t)
            """
            print(mline.wkt)
            print(mp.wkt_at(t))
            print(out)
        else:
            eq = False

def get_samples_for_viz_2(MS, mp, i, n_samples, s):
    n = (n_samples - 1)
    k = 0
    dt = i.y - i.x
    eq = False

    for j in range(0, n_samples):
        t = i.x + dt * (float(j) / n)

        mline = get_mline(MS, t)

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    print(mline.wkt)
                    print(mp.wkt_at(t))
                    print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    print(mline.wkt)
                    print(mp.wkt_at(s[k]))
                    print(1)
                    k += 1

                    eq = True

        if not eq:
            print(mline.wkt)
            print(mp.wkt_at(t))
            print(0)
        else:
            eq = False

#-------------------------------------------------------------------
# Intersection information for printing.
#-------------------------------------------------------------------
def get_intersection_information(intersection_instants, msegs, mp, op):
    """
    for e in intersection_instants:
        if isinstance(e, Interval):
            print(e.to_string())
        else:
            print(e)
    """
    add_comma = False
    #info = "NI: " + str(len(intersection_instants)) + " :: {"
    #info = "NI: " + str(len(intersection_instants)) + " >> "

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
    elif op == STOperation.Intersection.value:
        info = "Intersection: "

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

            #info += 't0: ' + format(t.x, precision) + ", x: " + format(P0x, precision) + ', y: ' + format(P0y, precision)
            info += format(t.x, precision) + ", " + format(t.y, precision)
            #info += ', '
            #info += 't1: ' + format(t.y, precision) + ", x: " + format(P1x, precision) + ', y: ' + format(P1y, precision)

            if t.r:
                info += ']'
            else:
                info += '['

            #info += ' >> ' + "(x: " + format(P0x, precision) + ', y: ' + format(P0y, precision) + '), '
            #info += "(x: " + format(P1x, precision) + ', y: ' + format(P1y, precision) + ')'
        else:
            Px, Py = mp.at(t)
			
            info += 't: ' + format(t, precision) #+ " >> (x: " + format(Px, precision) + ', y: ' + format(Py, precision) + ')'
            #info += 't: ' + format(t, precision) + " >> (x: " + format(Px, precision) + ', y: ' + format(Py, precision) + ')'

    #info += "}"
    return info

#-------------------------------------------------------------------
# Executes the solver.
#-------------------------------------------------------------------
def get_solutions(f, t, it):
    global eps

    #print(f)
    #print(it.to_string())
    #print(SpyInterval(it.x, it.y))
    s_exec_time = time.time()
    r = solveset(f, t, SpyInterval(it.x - eps, it.y + eps))
    e_exec_time = time.time()

    #print(r)

    solver_exec_time = e_exec_time - s_exec_time

    if r == S.Complexes:
        print("S.Complexes: Multiple intersections?")
        sys.exit()
    elif type(r) is SpyInterval:
        print(r.boundary, '>')
        #r = [Interval(r.start, r.end, r.left_open, r.right_open)]
        #sys.exit()
        r = [r.start, r.end]

    # I believe that the result may contain only real solutions since the domain is (explicitly) real?
    #print(r)
    r = [re(_r) for _r in r if im(_r) == 0]
    r.sort()

    #print(r)

    if len(r) == 1:
        if r[0] >= it.x - eps and r[0] <= it.x + eps:
            r[0] = it.x
        elif r[0] >= it.y - eps and r[0] <= it.y + eps:
            r[0] = it.y
    elif len(r) > 1:
        if r[0] >= it.x - eps and r[0] <= it.x + eps:
            r[0] = it.x

        if r[len(r)-1] >= it.y - eps and r[len(r)-1] <= it.y + eps:
            r[len(r)-1] = it.y

    #print(r)
    return solver_exec_time, r

def get_solutions_quartic(a, b, c, g, h, l, r, q, f, m, n, o, d, s, x, y, w, z, v, k, it):
    global eps
    """
    print('')
    print(a, b, c, g, h, l, r, q, f, m, n, o, d, s, x, y, w, z, v, k)
    print('')
    """
    s_exec_time = time.time()

    a0 = (a*d**4*k*m - a*d**4*k*y + a*d**4*v*z + 4*a*d**3*k*m*s - 2*a*d**3*k*n*s - 2*a*d**3*k*s*y + 2*a*d**3*s*v*z + 6*a*d**2*k*m*s**2 - 6*a*d**2*k*n*s**2 + a*d**2*k*o*s**2 - a*d**2*k*s**2*y + a*d**2*s**2*v*z + 4*a*d*k*m*s**3 - 6*a*d*k*n*s**3 + 2*a*d*k*o*s**3 + a*k*m*s**4 - 2*a*k*n*s**4 + a*k*o*s**4 - 2*b*d**3*k*m*s + 2*b*d**3*k*s*y - 2*b*d**3*s*v*z - 6*b*d**2*k*m*s**2 + 4*b*d**2*k*n*s**2 + 2*b*d**2*k*s**2*y - 2*b*d**2*s**2*v*z - 6*b*d*k*m*s**3 + 8*b*d*k*n*s**3 - 2*b*d*k*o*s**3 - 2*b*k*m*s**4 + 4*b*k*n*s**4 - 2*b*k*o*s**4 + c*d**2*k*m*s**2 - c*d**2*k*s**2*y + c*d**2*s**2*v*z + 2*c*d*k*m*s**3 - 2*c*d*k*n*s**3 + c*k*m*s**4 - 2*c*k*n*s**4 + c*k*o*s**4 - d**4*g*k*r + d**4*g*k*x - d**4*g*v*w - d**4*k*m*x + d**4*k*r*y + d**4*m*v*w - d**4*r*v*z + 2*d**3*g*k*q*s - 4*d**3*g*k*r*s + 2*d**3*g*k*s*x - 2*d**3*g*s*v*w + 2*d**3*h*k*r*s - 2*d**3*h*k*s*x + 2*d**3*h*s*v*w - 2*d**3*k*m*s*x + 2*d**3*k*n*s*x - 2*d**3*k*q*s*y + 2*d**3*k*r*s*y + 2*d**3*m*s*v*w - 2*d**3*n*s*v*w + 2*d**3*q*s*v*z - 2*d**3*r*s*v*z - d**2*f*g*k*s**2 + d**2*f*k*s**2*y - d**2*f*s**2*v*z + 6*d**2*g*k*q*s**2 - 6*d**2*g*k*r*s**2 + d**2*g*k*s**2*x - d**2*g*s**2*v*w - 4*d**2*h*k*q*s**2 + 6*d**2*h*k*r*s**2 - 2*d**2*h*k*s**2*x + 2*d**2*h*s**2*v*w - d**2*k*l*r*s**2 + d**2*k*l*s**2*x - d**2*k*m*s**2*x + 2*d**2*k*n*s**2*x - d**2*k*o*s**2*x - 2*d**2*k*q*s**2*y + d**2*k*r*s**2*y - d**2*l*s**2*v*w + d**2*m*s**2*v*w - 2*d**2*n*s**2*v*w + d**2*o*s**2*v*w + 2*d**2*q*s**2*v*z - d**2*r*s**2*v*z - 2*d*f*g*k*s**3 + 2*d*f*h*k*s**3 + 6*d*g*k*q*s**3 - 4*d*g*k*r*s**3 - 8*d*h*k*q*s**3 + 6*d*h*k*r*s**3 + 2*d*k*l*q*s**3 - 2*d*k*l*r*s**3 - f*g*k*s**4 + 2*f*h*k*s**4 - f*k*l*s**4 + 2*g*k*q*s**4 - g*k*r*s**4 - 4*h*k*q*s**4 + 2*h*k*r*s**4 + 2*k*l*q*s**4 - k*l*r*s**4) / (d**4*k)
    a1 = (-a*d**4*z - 4*a*d**3*k*m + 2*a*d**3*k*n + 2*a*d**3*k*y - 2*a*d**3*s*z - 2*a*d**3*v*z - 12*a*d**2*k*m*s + 12*a*d**2*k*n*s - 2*a*d**2*k*o*s + 2*a*d**2*k*s*y - a*d**2*s**2*z - 2*a*d**2*s*v*z - 12*a*d*k*m*s**2 + 18*a*d*k*n*s**2 - 6*a*d*k*o*s**2 - 4*a*k*m*s**3 + 8*a*k*n*s**3 - 4*a*k*o*s**3 + 2*b*d**3*k*m - 2*b*d**3*k*y + 2*b*d**3*s*z + 2*b*d**3*v*z + 12*b*d**2*k*m*s - 8*b*d**2*k*n*s - 4*b*d**2*k*s*y + 2*b*d**2*s**2*z + 4*b*d**2*s*v*z + 18*b*d*k*m*s**2 - 24*b*d*k*n*s**2 + 6*b*d*k*o*s**2 + 8*b*k*m*s**3 - 16*b*k*n*s**3 + 8*b*k*o*s**3 - 2*c*d**2*k*m*s + 2*c*d**2*k*s*y - c*d**2*s**2*z - 2*c*d**2*s*v*z - 6*c*d*k*m*s**2 + 6*c*d*k*n*s**2 - 4*c*k*m*s**3 + 8*c*k*n*s**3 - 4*c*k*o*s**3 + d**4*g*w - d**4*m*w + d**4*r*z - 2*d**3*g*k*q + 4*d**3*g*k*r - 2*d**3*g*k*x + 2*d**3*g*s*w + 2*d**3*g*v*w - 2*d**3*h*k*r + 2*d**3*h*k*x - 2*d**3*h*s*w - 2*d**3*h*v*w + 2*d**3*k*m*x - 2*d**3*k*n*x + 2*d**3*k*q*y - 2*d**3*k*r*y - 2*d**3*m*s*w - 2*d**3*m*v*w + 2*d**3*n*s*w + 2*d**3*n*v*w - 2*d**3*q*s*z - 2*d**3*q*v*z + 2*d**3*r*s*z + 2*d**3*r*v*z + 2*d**2*f*g*k*s - 2*d**2*f*k*s*y + d**2*f*s**2*z + 2*d**2*f*s*v*z - 12*d**2*g*k*q*s + 12*d**2*g*k*r*s - 2*d**2*g*k*s*x + d**2*g*s**2*w + 2*d**2*g*s*v*w + 8*d**2*h*k*q*s - 12*d**2*h*k*r*s + 4*d**2*h*k*s*x - 2*d**2*h*s**2*w - 4*d**2*h*s*v*w + 2*d**2*k*l*r*s - 2*d**2*k*l*s*x + 2*d**2*k*m*s*x - 4*d**2*k*n*s*x + 2*d**2*k*o*s*x + 4*d**2*k*q*s*y - 2*d**2*k*r*s*y + d**2*l*s**2*w + 2*d**2*l*s*v*w - d**2*m*s**2*w - 2*d**2*m*s*v*w + 2*d**2*n*s**2*w + 4*d**2*n*s*v*w - d**2*o*s**2*w - 2*d**2*o*s*v*w - 2*d**2*q*s**2*z - 4*d**2*q*s*v*z + d**2*r*s**2*z + 2*d**2*r*s*v*z + 6*d*f*g*k*s**2 - 6*d*f*h*k*s**2 - 18*d*g*k*q*s**2 + 12*d*g*k*r*s**2 + 24*d*h*k*q*s**2 - 18*d*h*k*r*s**2 - 6*d*k*l*q*s**2 + 6*d*k*l*r*s**2 + 4*f*g*k*s**3 - 8*f*h*k*s**3 + 4*f*k*l*s**3 - 8*g*k*q*s**3 + 4*g*k*r*s**3 + 16*h*k*q*s**3 - 8*h*k*r*s**3 - 8*k*l*q*s**3 + 4*k*l*r*s**3 ) / (d**4*k)
    a2 = (2*a*d**3*z + 6*a*d**2*k*m - 6*a*d**2*k*n + a*d**2*k*o - a*d**2*k*y + 2*a*d**2*s*z + a*d**2*v*z + 12*a*d*k*m*s - 18*a*d*k*n*s + 6*a*d*k*o*s + 6*a*k*m*s**2 - 12*a*k*n*s**2 + 6*a*k*o*s**2 - 2*b*d**3*z - 6*b*d**2*k*m + 4*b*d**2*k*n + 2*b*d**2*k*y - 4*b*d**2*s*z - 2*b*d**2*v*z - 18*b*d*k*m*s + 24*b*d*k*n*s - 6*b*d*k*o*s - 12*b*k*m*s**2 + 24*b*k*n*s**2 - 12*b*k*o*s**2 + c*d**2*k*m - c*d**2*k*y + 2*c*d**2*s*z + c*d**2*v*z + 6*c*d*k*m*s - 6*c*d*k*n*s + 6*c*k*m*s**2 - 12*c*k*n*s**2 + 6*c*k*o*s**2 - 2*d**3*g*w + 2*d**3*h*w + 2*d**3*m*w - 2*d**3*n*w + 2*d**3*q*z - 2*d**3*r*z - d**2*f*g*k + d**2*f*k*y - 2*d**2*f*s*z - d**2*f*v*z + 6*d**2*g*k*q - 6*d**2*g*k*r + d**2*g*k*x - 2*d**2*g*s*w - d**2*g*v*w - 4*d**2*h*k*q + 6*d**2*h*k*r - 2*d**2*h*k*x + 4*d**2*h*s*w + 2*d**2*h*v*w - d**2*k*l*r + d**2*k*l*x - d**2*k*m*x + 2*d**2*k*n*x - d**2*k*o*x - 2*d**2*k*q*y + d**2*k*r*y - 2*d**2*l*s*w - d**2*l*v*w + 2*d**2*m*s*w + d**2*m*v*w - 4*d**2*n*s*w - 2*d**2*n*v*w + 2*d**2*o*s*w + d**2*o*v*w + 4*d**2*q*s*z + 2*d**2*q*v*z - 2*d**2*r*s*z - d**2*r*v*z - 6*d*f*g*k*s + 6*d*f*h*k*s + 18*d*g*k*q*s - 12*d*g*k*r*s - 24*d*h*k*q*s + 18*d*h*k*r*s + 6*d*k*l*q*s - 6*d*k*l*r*s - 6*f*g*k*s**2 + 12*f*h*k*s**2 - 6*f*k*l*s**2 + 12*g*k*q*s**2 - 6*g*k*r*s**2 - 24*h*k*q*s**2 + 12*h*k*r*s**2 + 12*k*l*q*s**2 - 6*k*l*r*s**2 ) / (d**4*k)
    a3 = (-a*d**2*z - 4*a*d*k*m + 6*a*d*k*n - 2*a*d*k*o - 4*a*k*m*s + 8*a*k*n*s - 4*a*k*o*s + 2*b*d**2*z + 6*b*d*k*m - 8*b*d*k*n + 2*b*d*k*o + 8*b*k*m*s - 16*b*k*n*s + 8*b*k*o*s - c*d**2*z - 2*c*d*k*m + 2*c*d*k*n - 4*c*k*m*s + 8*c*k*n*s - 4*c*k*o*s + d**2*f*z + d**2*g*w - 2*d**2*h*w + d**2*l*w - d**2*m*w + 2*d**2*n*w - d**2*o*w - 2*d**2*q*z + d**2*r*z + 2*d*f*g*k - 2*d*f*h*k - 6*d*g*k*q + 4*d*g*k*r + 8*d*h*k*q - 6*d*h*k*r - 2*d*k*l*q + 2*d*k*l*r + 4*f*g*k*s - 8*f*h*k*s + 4*f*k*l*s - 8*g*k*q*s + 4*g*k*r*s + 16*h*k*q*s - 8*h*k*r*s - 8*k*l*q*s + 4*k*l*r*s ) / (d**4*k)
    a4 = (a*k*m - 2*a*k*n + a*k*o - 2*b*k*m + 4*b*k*n - 2*b*k*o + c*k*m - 2*c*k*n + c*k*o - f*g*k + 2*f*h*k - f*k*l + 2*g*k*q - g*k*r - 4*h*k*q + 2*h*k*r + 2*k*l*q - k*l*r ) / (d**4*k)

    coeff = [a4]
    coeff += [a3]
    coeff += [a2]
    coeff += [a1]
    coeff += [a0]

    r = np.roots(coeff)
    e_exec_time = time.time()

    solver_exec_time = e_exec_time - s_exec_time
    """
    if r == S.Complexes:
        print("S.Complexes: Multiple intersections?")
        sys.exit()
    elif type(r) is SpyInterval:
        print(r)
        sys.exit()
    """
    # I believe that the result may contain only real solutions since the domain is (explicitly) real?
    #r = [re(_r) for _r in r if im(_r) == 0 and _r >= 0 and _r <= 1]
    r = [re(_r) for _r in r if im(_r) == 0]
    r.sort()

    #print(r, it.x, it.y)

    N = len(r)
    K = 0

    while K < N:
        if r[K] >= it.x - eps and r[K] <= it.x + eps:
            r[K] = it.x
        elif r[K] >= it.y - eps and r[K] <= it.y + eps:
            r[K] = it.y

        K += 1

    K = 0
    _r = []

    while K < N:
        if r[K] >= it.x and r[K] <= it.y:
            _r += [r[K]]

        K += 1

    r = _r

    """
    if len(r) == 1:
        if r[0] >= it.x - eps and r[0] <= it.x + eps:
            r[0] = it.x
        elif r[0] >= it.y - eps and r[0] <= it.y + eps:
            r[0] = it.y
    elif len(r) > 1:
        if r[0] >= it.x - eps and r[0] <= it.x + eps:
            r[0] = it.x

        if r[len(r)-1] >= it.y - eps and r[len(r)-1] <= it.y + eps:
            r[len(r)-1] = it.y
    """

    #print(r, it.x, it.y)

    #print(r)
    return solver_exec_time, r

def get_solutions_quartic2(a, b, c, g, h, l, r, q, f, m, n, o, d, s, w, v, y, x, k, u, z, p, it):
    global eps

    s_exec_time = time.time()

    #a0 = (a*d**4*k*m - a*d**4*k*y + a*d**4*v*z + 4*a*d**3*k*m*s - 2*a*d**3*k*n*s - 2*a*d**3*k*s*y + 2*a*d**3*s*v*z + 6*a*d**2*k*m*s**2 - 6*a*d**2*k*n*s**2 + a*d**2*k*o*s**2 - a*d**2*k*s**2*y + a*d**2*s**2*v*z + 4*a*d*k*m*s**3 - 6*a*d*k*n*s**3 + 2*a*d*k*o*s**3 + a*k*m*s**4 - 2*a*k*n*s**4 + a*k*o*s**4 - 2*b*d**3*k*m*s + 2*b*d**3*k*s*y - 2*b*d**3*s*v*z - 6*b*d**2*k*m*s**2 + 4*b*d**2*k*n*s**2 + 2*b*d**2*k*s**2*y - 2*b*d**2*s**2*v*z - 6*b*d*k*m*s**3 + 8*b*d*k*n*s**3 - 2*b*d*k*o*s**3 - 2*b*k*m*s**4 + 4*b*k*n*s**4 - 2*b*k*o*s**4 + c*d**2*k*m*s**2 - c*d**2*k*s**2*y + c*d**2*s**2*v*z + 2*c*d*k*m*s**3 - 2*c*d*k*n*s**3 + c*k*m*s**4 - 2*c*k*n*s**4 + c*k*o*s**4 - d**4*g*k*r + d**4*g*k*x - d**4*g*v*w - d**4*k*m*x + d**4*k*r*y + d**4*m*v*w - d**4*r*v*z + 2*d**3*g*k*q*s - 4*d**3*g*k*r*s + 2*d**3*g*k*s*x - 2*d**3*g*s*v*w + 2*d**3*h*k*r*s - 2*d**3*h*k*s*x + 2*d**3*h*s*v*w - 2*d**3*k*m*s*x + 2*d**3*k*n*s*x - 2*d**3*k*q*s*y + 2*d**3*k*r*s*y + 2*d**3*m*s*v*w - 2*d**3*n*s*v*w + 2*d**3*q*s*v*z - 2*d**3*r*s*v*z - d**2*f*g*k*s**2 + d**2*f*k*s**2*y - d**2*f*s**2*v*z + 6*d**2*g*k*q*s**2 - 6*d**2*g*k*r*s**2 + d**2*g*k*s**2*x - d**2*g*s**2*v*w - 4*d**2*h*k*q*s**2 + 6*d**2*h*k*r*s**2 - 2*d**2*h*k*s**2*x + 2*d**2*h*s**2*v*w - d**2*k*l*r*s**2 + d**2*k*l*s**2*x - d**2*k*m*s**2*x + 2*d**2*k*n*s**2*x - d**2*k*o*s**2*x - 2*d**2*k*q*s**2*y + d**2*k*r*s**2*y - d**2*l*s**2*v*w + d**2*m*s**2*v*w - 2*d**2*n*s**2*v*w + d**2*o*s**2*v*w + 2*d**2*q*s**2*v*z - d**2*r*s**2*v*z - 2*d*f*g*k*s**3 + 2*d*f*h*k*s**3 + 6*d*g*k*q*s**3 - 4*d*g*k*r*s**3 - 8*d*h*k*q*s**3 + 6*d*h*k*r*s**3 + 2*d*k*l*q*s**3 - 2*d*k*l*r*s**3 - f*g*k*s**4 + 2*f*h*k*s**4 - f*k*l*s**4 + 2*g*k*q*s**4 - g*k*r*s**4 - 4*h*k*q*s**4 + 2*h*k*r*s**4 + 2*k*l*q*s**4 - k*l*r*s**4) / (d**4*k)
    #a1 = (-a*d**4*z - 4*a*d**3*k*m + 2*a*d**3*k*n + 2*a*d**3*k*y - 2*a*d**3*s*z - 2*a*d**3*v*z - 12*a*d**2*k*m*s + 12*a*d**2*k*n*s - 2*a*d**2*k*o*s + 2*a*d**2*k*s*y - a*d**2*s**2*z - 2*a*d**2*s*v*z - 12*a*d*k*m*s**2 + 18*a*d*k*n*s**2 - 6*a*d*k*o*s**2 - 4*a*k*m*s**3 + 8*a*k*n*s**3 - 4*a*k*o*s**3 + 2*b*d**3*k*m - 2*b*d**3*k*y + 2*b*d**3*s*z + 2*b*d**3*v*z + 12*b*d**2*k*m*s - 8*b*d**2*k*n*s - 4*b*d**2*k*s*y + 2*b*d**2*s**2*z + 4*b*d**2*s*v*z + 18*b*d*k*m*s**2 - 24*b*d*k*n*s**2 + 6*b*d*k*o*s**2 + 8*b*k*m*s**3 - 16*b*k*n*s**3 + 8*b*k*o*s**3 - 2*c*d**2*k*m*s + 2*c*d**2*k*s*y - c*d**2*s**2*z - 2*c*d**2*s*v*z - 6*c*d*k*m*s**2 + 6*c*d*k*n*s**2 - 4*c*k*m*s**3 + 8*c*k*n*s**3 - 4*c*k*o*s**3 + d**4*g*w - d**4*m*w + d**4*r*z - 2*d**3*g*k*q + 4*d**3*g*k*r - 2*d**3*g*k*x + 2*d**3*g*s*w + 2*d**3*g*v*w - 2*d**3*h*k*r + 2*d**3*h*k*x - 2*d**3*h*s*w - 2*d**3*h*v*w + 2*d**3*k*m*x - 2*d**3*k*n*x + 2*d**3*k*q*y - 2*d**3*k*r*y - 2*d**3*m*s*w - 2*d**3*m*v*w + 2*d**3*n*s*w + 2*d**3*n*v*w - 2*d**3*q*s*z - 2*d**3*q*v*z + 2*d**3*r*s*z + 2*d**3*r*v*z + 2*d**2*f*g*k*s - 2*d**2*f*k*s*y + d**2*f*s**2*z + 2*d**2*f*s*v*z - 12*d**2*g*k*q*s + 12*d**2*g*k*r*s - 2*d**2*g*k*s*x + d**2*g*s**2*w + 2*d**2*g*s*v*w + 8*d**2*h*k*q*s - 12*d**2*h*k*r*s + 4*d**2*h*k*s*x - 2*d**2*h*s**2*w - 4*d**2*h*s*v*w + 2*d**2*k*l*r*s - 2*d**2*k*l*s*x + 2*d**2*k*m*s*x - 4*d**2*k*n*s*x + 2*d**2*k*o*s*x + 4*d**2*k*q*s*y - 2*d**2*k*r*s*y + d**2*l*s**2*w + 2*d**2*l*s*v*w - d**2*m*s**2*w - 2*d**2*m*s*v*w + 2*d**2*n*s**2*w + 4*d**2*n*s*v*w - d**2*o*s**2*w - 2*d**2*o*s*v*w - 2*d**2*q*s**2*z - 4*d**2*q*s*v*z + d**2*r*s**2*z + 2*d**2*r*s*v*z + 6*d*f*g*k*s**2 - 6*d*f*h*k*s**2 - 18*d*g*k*q*s**2 + 12*d*g*k*r*s**2 + 24*d*h*k*q*s**2 - 18*d*h*k*r*s**2 - 6*d*k*l*q*s**2 + 6*d*k*l*r*s**2 + 4*f*g*k*s**3 - 8*f*h*k*s**3 + 4*f*k*l*s**3 - 8*g*k*q*s**3 + 4*g*k*r*s**3 + 16*h*k*q*s**3 - 8*h*k*r*s**3 - 8*k*l*q*s**3 + 4*k*l*r*s**3 ) / (d**4*k)
    #a2 = (2*a*d**3*z + 6*a*d**2*k*m - 6*a*d**2*k*n + a*d**2*k*o - a*d**2*k*y + 2*a*d**2*s*z + a*d**2*v*z + 12*a*d*k*m*s - 18*a*d*k*n*s + 6*a*d*k*o*s + 6*a*k*m*s**2 - 12*a*k*n*s**2 + 6*a*k*o*s**2 - 2*b*d**3*z - 6*b*d**2*k*m + 4*b*d**2*k*n + 2*b*d**2*k*y - 4*b*d**2*s*z - 2*b*d**2*v*z - 18*b*d*k*m*s + 24*b*d*k*n*s - 6*b*d*k*o*s - 12*b*k*m*s**2 + 24*b*k*n*s**2 - 12*b*k*o*s**2 + c*d**2*k*m - c*d**2*k*y + 2*c*d**2*s*z + c*d**2*v*z + 6*c*d*k*m*s - 6*c*d*k*n*s + 6*c*k*m*s**2 - 12*c*k*n*s**2 + 6*c*k*o*s**2 - 2*d**3*g*w + 2*d**3*h*w + 2*d**3*m*w - 2*d**3*n*w + 2*d**3*q*z - 2*d**3*r*z - d**2*f*g*k + d**2*f*k*y - 2*d**2*f*s*z - d**2*f*v*z + 6*d**2*g*k*q - 6*d**2*g*k*r + d**2*g*k*x - 2*d**2*g*s*w - d**2*g*v*w - 4*d**2*h*k*q + 6*d**2*h*k*r - 2*d**2*h*k*x + 4*d**2*h*s*w + 2*d**2*h*v*w - d**2*k*l*r + d**2*k*l*x - d**2*k*m*x + 2*d**2*k*n*x - d**2*k*o*x - 2*d**2*k*q*y + d**2*k*r*y - 2*d**2*l*s*w - d**2*l*v*w + 2*d**2*m*s*w + d**2*m*v*w - 4*d**2*n*s*w - 2*d**2*n*v*w + 2*d**2*o*s*w + d**2*o*v*w + 4*d**2*q*s*z + 2*d**2*q*v*z - 2*d**2*r*s*z - d**2*r*v*z - 6*d*f*g*k*s + 6*d*f*h*k*s + 18*d*g*k*q*s - 12*d*g*k*r*s - 24*d*h*k*q*s + 18*d*h*k*r*s + 6*d*k*l*q*s - 6*d*k*l*r*s - 6*f*g*k*s**2 + 12*f*h*k*s**2 - 6*f*k*l*s**2 + 12*g*k*q*s**2 - 6*g*k*r*s**2 - 24*h*k*q*s**2 + 12*h*k*r*s**2 + 12*k*l*q*s**2 - 6*k*l*r*s**2 ) / (d**4*k)
    #a3 = (-a*d**2*z - 4*a*d*k*m + 6*a*d*k*n - 2*a*d*k*o - 4*a*k*m*s + 8*a*k*n*s - 4*a*k*o*s + 2*b*d**2*z + 6*b*d*k*m - 8*b*d*k*n + 2*b*d*k*o + 8*b*k*m*s - 16*b*k*n*s + 8*b*k*o*s - c*d**2*z - 2*c*d*k*m + 2*c*d*k*n - 4*c*k*m*s + 8*c*k*n*s - 4*c*k*o*s + d**2*f*z + d**2*g*w - 2*d**2*h*w + d**2*l*w - d**2*m*w + 2*d**2*n*w - d**2*o*w - 2*d**2*q*z + d**2*r*z + 2*d*f*g*k - 2*d*f*h*k - 6*d*g*k*q + 4*d*g*k*r + 8*d*h*k*q - 6*d*h*k*r - 2*d*k*l*q + 2*d*k*l*r + 4*f*g*k*s - 8*f*h*k*s + 4*f*k*l*s - 8*g*k*q*s + 4*g*k*r*s + 16*h*k*q*s - 8*h*k*r*s - 8*k*l*q*s + 4*k*l*r*s ) / (d**4*k)
    #a4 = (a*k*m - 2*a*k*n + a*k*o - 2*b*k*m + 4*b*k*n - 2*b*k*o + c*k*m - 2*c*k*n + c*k*o - f*g*k + 2*f*h*k - f*k*l + 2*g*k*q - g*k*r - 4*h*k*q + 2*h*k*r + 2*k*l*q - k*l*r ) / (d**4*k)

    a0 = (+2*a*d**4*k*p*z + 2*a*d**4*k*z**2 + a*d**4*m*p**2 - a*d**4*p**2*x - 2*a*d**4*p*x*z - a*d**4*u*z**2 - a*d**4*x*z**2 + 4*a*d**3*k*p*s*z + 4*a*d**3*k*s*z**2 + 4*a*d**3*m*p**2*s - 2*a*d**3*n*p**2*s - 2*a*d**3*p**2*s*x - 4*a*d**3*p*s*x*z - 2*a*d**3*s*u*z**2 - 2*a*d**3*s*x*z**2 + 2*a*d**2*k*p*s**2*z + 2*a*d**2*k*s**2*z**2 + 6*a*d**2*m*p**2*s**2 - 6*a*d**2*n*p**2*s**2 + a*d**2*o*p**2*s**2 - a*d**2*p**2*s**2*x - 2*a*d**2*p*s**2*x*z - a*d**2*s**2*u*z**2 - a*d**2*s**2*x*z**2 + 4*a*d*m*p**2*s**3 - 6*a*d*n*p**2*s**3 + 2*a*d*o*p**2*s**3 + a*m*p**2*s**4 - 2*a*n*p**2*s**4 + a*o*p**2*s**4 - 4*b*d**3*k*p*s*z - 4*b*d**3*k*s*z**2 - 2*b*d**3*m*p**2*s + 2*b*d**3*p**2*s*x + 4*b*d**3*p*s*x*z + 2*b*d**3*s*u*z**2 + 2*b*d**3*s*x*z**2 - 4*b*d**2*k*p*s**2*z - 4*b*d**2*k*s**2*z**2 - 6*b*d**2*m*p**2*s**2 + 4*b*d**2*n*p**2*s**2 + 2*b*d**2*p**2*s**2*x + 4*b*d**2*p*s**2*x*z + 2*b*d**2*s**2*u*z**2 + 2*b*d**2*s**2*x*z**2 - 6*b*d*m*p**2*s**3 + 8*b*d*n*p**2*s**3 - 2*b*d*o*p**2*s**3 - 2*b*m*p**2*s**4 + 4*b*n*p**2*s**4 - 2*b*o*p**2*s**4 + 2*c*d**2*k*p*s**2*z + 2*c*d**2*k*s**2*z**2 + c*d**2*m*p**2*s**2 - c*d**2*p**2*s**2*x - 2*c*d**2*p*s**2*x*z - c*d**2*s**2*u*z**2 - c*d**2*s**2*x*z**2 + 2*c*d*m*p**2*s**3 - 2*c*d*n*p**2*s**3 + c*m*p**2*s**4 - 2*c*n*p**2*s**4 + c*o*p**2*s**4 - d**4*g*p**2*r + d**4*g*p**2*w - 2*d**4*g*p*v*z + 2*d**4*g*p*w*z - 2*d**4*g*v*z**2 + d**4*g*w*z**2 + d**4*g*y*z**2 - 2*d**4*k*p*r*z - 2*d**4*k*r*z**2 - d**4*m*p**2*w + 2*d**4*m*p*v*z - 2*d**4*m*p*w*z + 2*d**4*m*v*z**2 - d**4*m*w*z**2 - d**4*m*y*z**2 + d**4*p**2*r*x + 2*d**4*p*r*x*z + d**4*r*u*z**2 + d**4*r*x*z**2 + 2*d**3*g*p**2*q*s - 4*d**3*g*p**2*r*s + 2*d**3*g*p**2*s*w - 4*d**3*g*p*s*v*z + 4*d**3*g*p*s*w*z - 4*d**3*g*s*v*z**2 + 2*d**3*g*s*w*z**2 + 2*d**3*g*s*y*z**2 + 2*d**3*h*p**2*r*s - 2*d**3*h*p**2*s*w + 4*d**3*h*p*s*v*z - 4*d**3*h*p*s*w*z + 4*d**3*h*s*v*z**2 - 2*d**3*h*s*w*z**2 - 2*d**3*h*s*y*z**2 + 4*d**3*k*p*q*s*z - 4*d**3*k*p*r*s*z + 4*d**3*k*q*s*z**2 - 4*d**3*k*r*s*z**2 - 2*d**3*m*p**2*s*w + 4*d**3*m*p*s*v*z - 4*d**3*m*p*s*w*z + 4*d**3*m*s*v*z**2 - 2*d**3*m*s*w*z**2 - 2*d**3*m*s*y*z**2 + 2*d**3*n*p**2*s*w - 4*d**3*n*p*s*v*z + 4*d**3*n*p*s*w*z - 4*d**3*n*s*v*z**2 + 2*d**3*n*s*w*z**2 + 2*d**3*n*s*y*z**2 - 2*d**3*p**2*q*s*x + 2*d**3*p**2*r*s*x - 4*d**3*p*q*s*x*z + 4*d**3*p*r*s*x*z - 2*d**3*q*s*u*z**2 - 2*d**3*q*s*x*z**2 + 2*d**3*r*s*u*z**2 + 2*d**3*r*s*x*z**2 - d**2*f*g*p**2*s**2 - 2*d**2*f*k*p*s**2*z - 2*d**2*f*k*s**2*z**2 + d**2*f*p**2*s**2*x + 2*d**2*f*p*s**2*x*z + d**2*f*s**2*u*z**2 + d**2*f*s**2*x*z**2 + 6*d**2*g*p**2*q*s**2 - 6*d**2*g*p**2*r*s**2 + d**2*g*p**2*s**2*w - 2*d**2*g*p*s**2*v*z + 2*d**2*g*p*s**2*w*z - 2*d**2*g*s**2*v*z**2 + d**2*g*s**2*w*z**2 + d**2*g*s**2*y*z**2 - 4*d**2*h*p**2*q*s**2 + 6*d**2*h*p**2*r*s**2 - 2*d**2*h*p**2*s**2*w + 4*d**2*h*p*s**2*v*z - 4*d**2*h*p*s**2*w*z + 4*d**2*h*s**2*v*z**2 - 2*d**2*h*s**2*w*z**2 - 2*d**2*h*s**2*y*z**2 + 4*d**2*k*p*q*s**2*z - 2*d**2*k*p*r*s**2*z + 4*d**2*k*q*s**2*z**2 - 2*d**2*k*r*s**2*z**2 - d**2*l*p**2*r*s**2 + d**2*l*p**2*s**2*w - 2*d**2*l*p*s**2*v*z + 2*d**2*l*p*s**2*w*z - 2*d**2*l*s**2*v*z**2 + d**2*l*s**2*w*z**2 + d**2*l*s**2*y*z**2 - d**2*m*p**2*s**2*w + 2*d**2*m*p*s**2*v*z - 2*d**2*m*p*s**2*w*z + 2*d**2*m*s**2*v*z**2 - d**2*m*s**2*w*z**2 - d**2*m*s**2*y*z**2 + 2*d**2*n*p**2*s**2*w - 4*d**2*n*p*s**2*v*z + 4*d**2*n*p*s**2*w*z - 4*d**2*n*s**2*v*z**2 + 2*d**2*n*s**2*w*z**2 + 2*d**2*n*s**2*y*z**2 - d**2*o*p**2*s**2*w + 2*d**2*o*p*s**2*v*z - 2*d**2*o*p*s**2*w*z + 2*d**2*o*s**2*v*z**2 - d**2*o*s**2*w*z**2 - d**2*o*s**2*y*z**2 - 2*d**2*p**2*q*s**2*x + d**2*p**2*r*s**2*x - 4*d**2*p*q*s**2*x*z + 2*d**2*p*r*s**2*x*z - 2*d**2*q*s**2*u*z**2 - 2*d**2*q*s**2*x*z**2 + d**2*r*s**2*u*z**2 + d**2*r*s**2*x*z**2 - 2*d*f*g*p**2*s**3 + 2*d*f*h*p**2*s**3 + 6*d*g*p**2*q*s**3 - 4*d*g*p**2*r*s**3 - 8*d*h*p**2*q*s**3 + 6*d*h*p**2*r*s**3 + 2*d*l*p**2*q*s**3 - 2*d*l*p**2*r*s**3 - f*g*p**2*s**4 + 2*f*h*p**2*s**4 - f*l*p**2*s**4 + 2*g*p**2*q*s**4 - g*p**2*r*s**4 - 4*h*p**2*q*s**4 + 2*h*p**2*r*s**4 + 2*l*p**2*q*s**4 - l*p**2*r*s**4 ) / (d**4*p**2)
    a1 = (-2*a*d**4*k*p - 4*a*d**4*k*z + 2*a*d**4*p*x + 2*a*d**4*u*z + 2*a*d**4*x*z - 4*a*d**3*k*p*s - 4*a*d**3*k*p*z - 8*a*d**3*k*s*z - 4*a*d**3*k*z**2 - 4*a*d**3*m*p**2 + 2*a*d**3*n*p**2 + 2*a*d**3*p**2*x + 4*a*d**3*p*s*x + 4*a*d**3*p*x*z + 4*a*d**3*s*u*z + 4*a*d**3*s*x*z + 2*a*d**3*u*z**2 + 2*a*d**3*x*z**2 - 2*a*d**2*k*p*s**2 - 4*a*d**2*k*p*s*z - 4*a*d**2*k*s**2*z - 4*a*d**2*k*s*z**2 - 12*a*d**2*m*p**2*s + 12*a*d**2*n*p**2*s - 2*a*d**2*o*p**2*s + 2*a*d**2*p**2*s*x + 2*a*d**2*p*s**2*x + 4*a*d**2*p*s*x*z + 2*a*d**2*s**2*u*z + 2*a*d**2*s**2*x*z + 2*a*d**2*s*u*z**2 + 2*a*d**2*s*x*z**2 - 12*a*d*m*p**2*s**2 + 18*a*d*n*p**2*s**2 - 6*a*d*o*p**2*s**2 - 4*a*m*p**2*s**3 + 8*a*n*p**2*s**3 - 4*a*o*p**2*s**3 + 4*b*d**3*k*p*s + 4*b*d**3*k*p*z + 8*b*d**3*k*s*z + 4*b*d**3*k*z**2 + 2*b*d**3*m*p**2 - 2*b*d**3*p**2*x - 4*b*d**3*p*s*x - 4*b*d**3*p*x*z - 4*b*d**3*s*u*z - 4*b*d**3*s*x*z - 2*b*d**3*u*z**2 - 2*b*d**3*x*z**2 + 4*b*d**2*k*p*s**2 + 8*b*d**2*k*p*s*z + 8*b*d**2*k*s**2*z + 8*b*d**2*k*s*z**2 + 12*b*d**2*m*p**2*s - 8*b*d**2*n*p**2*s - 4*b*d**2*p**2*s*x - 4*b*d**2*p*s**2*x - 8*b*d**2*p*s*x*z - 4*b*d**2*s**2*u*z - 4*b*d**2*s**2*x*z - 4*b*d**2*s*u*z**2 - 4*b*d**2*s*x*z**2 + 18*b*d*m*p**2*s**2 - 24*b*d*n*p**2*s**2 + 6*b*d*o*p**2*s**2 + 8*b*m*p**2*s**3 - 16*b*n*p**2*s**3 + 8*b*o*p**2*s**3 - 2*c*d**2*k*p*s**2 - 4*c*d**2*k*p*s*z - 4*c*d**2*k*s**2*z - 4*c*d**2*k*s*z**2 - 2*c*d**2*m*p**2*s + 2*c*d**2*p**2*s*x + 2*c*d**2*p*s**2*x + 4*c*d**2*p*s*x*z + 2*c*d**2*s**2*u*z + 2*c*d**2*s**2*x*z + 2*c*d**2*s*u*z**2 + 2*c*d**2*s*x*z**2 - 6*c*d*m*p**2*s**2 + 6*c*d*n*p**2*s**2 - 4*c*m*p**2*s**3 + 8*c*n*p**2*s**3 - 4*c*o*p**2*s**3 + 2*d**4*g*p*v - 2*d**4*g*p*w + 4*d**4*g*v*z - 2*d**4*g*w*z - 2*d**4*g*y*z + 2*d**4*k*p*r + 4*d**4*k*r*z - 2*d**4*m*p*v + 2*d**4*m*p*w - 4*d**4*m*v*z + 2*d**4*m*w*z + 2*d**4*m*y*z - 2*d**4*p*r*x - 2*d**4*r*u*z - 2*d**4*r*x*z - 2*d**3*g*p**2*q + 4*d**3*g*p**2*r - 2*d**3*g*p**2*w + 4*d**3*g*p*s*v - 4*d**3*g*p*s*w + 4*d**3*g*p*v*z - 4*d**3*g*p*w*z + 8*d**3*g*s*v*z - 4*d**3*g*s*w*z - 4*d**3*g*s*y*z + 4*d**3*g*v*z**2 - 2*d**3*g*w*z**2 - 2*d**3*g*y*z**2 - 2*d**3*h*p**2*r + 2*d**3*h*p**2*w - 4*d**3*h*p*s*v + 4*d**3*h*p*s*w - 4*d**3*h*p*v*z + 4*d**3*h*p*w*z - 8*d**3*h*s*v*z + 4*d**3*h*s*w*z + 4*d**3*h*s*y*z - 4*d**3*h*v*z**2 + 2*d**3*h*w*z**2 + 2*d**3*h*y*z**2 - 4*d**3*k*p*q*s - 4*d**3*k*p*q*z + 4*d**3*k*p*r*s + 4*d**3*k*p*r*z - 8*d**3*k*q*s*z - 4*d**3*k*q*z**2 + 8*d**3*k*r*s*z + 4*d**3*k*r*z**2 + 2*d**3*m*p**2*w - 4*d**3*m*p*s*v + 4*d**3*m*p*s*w - 4*d**3*m*p*v*z + 4*d**3*m*p*w*z - 8*d**3*m*s*v*z + 4*d**3*m*s*w*z + 4*d**3*m*s*y*z - 4*d**3*m*v*z**2 + 2*d**3*m*w*z**2 + 2*d**3*m*y*z**2 - 2*d**3*n*p**2*w + 4*d**3*n*p*s*v - 4*d**3*n*p*s*w + 4*d**3*n*p*v*z - 4*d**3*n*p*w*z + 8*d**3*n*s*v*z - 4*d**3*n*s*w*z - 4*d**3*n*s*y*z + 4*d**3*n*v*z**2 - 2*d**3*n*w*z**2 - 2*d**3*n*y*z**2 + 2*d**3*p**2*q*x - 2*d**3*p**2*r*x + 4*d**3*p*q*s*x + 4*d**3*p*q*x*z - 4*d**3*p*r*s*x - 4*d**3*p*r*x*z + 4*d**3*q*s*u*z + 4*d**3*q*s*x*z + 2*d**3*q*u*z**2 + 2*d**3*q*x*z**2 - 4*d**3*r*s*u*z - 4*d**3*r*s*x*z - 2*d**3*r*u*z**2 - 2*d**3*r*x*z**2 + 2*d**2*f*g*p**2*s + 2*d**2*f*k*p*s**2 + 4*d**2*f*k*p*s*z + 4*d**2*f*k*s**2*z + 4*d**2*f*k*s*z**2 - 2*d**2*f*p**2*s*x - 2*d**2*f*p*s**2*x - 4*d**2*f*p*s*x*z - 2*d**2*f*s**2*u*z - 2*d**2*f*s**2*x*z - 2*d**2*f*s*u*z**2 - 2*d**2*f*s*x*z**2 - 12*d**2*g*p**2*q*s + 12*d**2*g*p**2*r*s - 2*d**2*g*p**2*s*w + 2*d**2*g*p*s**2*v - 2*d**2*g*p*s**2*w + 4*d**2*g*p*s*v*z - 4*d**2*g*p*s*w*z + 4*d**2*g*s**2*v*z - 2*d**2*g*s**2*w*z - 2*d**2*g*s**2*y*z + 4*d**2*g*s*v*z**2 - 2*d**2*g*s*w*z**2 - 2*d**2*g*s*y*z**2 + 8*d**2*h*p**2*q*s - 12*d**2*h*p**2*r*s + 4*d**2*h*p**2*s*w - 4*d**2*h*p*s**2*v + 4*d**2*h*p*s**2*w - 8*d**2*h*p*s*v*z + 8*d**2*h*p*s*w*z - 8*d**2*h*s**2*v*z + 4*d**2*h*s**2*w*z + 4*d**2*h*s**2*y*z - 8*d**2*h*s*v*z**2 + 4*d**2*h*s*w*z**2 + 4*d**2*h*s*y*z**2 - 4*d**2*k*p*q*s**2 - 8*d**2*k*p*q*s*z + 2*d**2*k*p*r*s**2 + 4*d**2*k*p*r*s*z - 8*d**2*k*q*s**2*z - 8*d**2*k*q*s*z**2 + 4*d**2*k*r*s**2*z + 4*d**2*k*r*s*z**2 + 2*d**2*l*p**2*r*s - 2*d**2*l*p**2*s*w + 2*d**2*l*p*s**2*v - 2*d**2*l*p*s**2*w + 4*d**2*l*p*s*v*z - 4*d**2*l*p*s*w*z + 4*d**2*l*s**2*v*z - 2*d**2*l*s**2*w*z - 2*d**2*l*s**2*y*z + 4*d**2*l*s*v*z**2 - 2*d**2*l*s*w*z**2 - 2*d**2*l*s*y*z**2 + 2*d**2*m*p**2*s*w - 2*d**2*m*p*s**2*v + 2*d**2*m*p*s**2*w - 4*d**2*m*p*s*v*z + 4*d**2*m*p*s*w*z - 4*d**2*m*s**2*v*z + 2*d**2*m*s**2*w*z + 2*d**2*m*s**2*y*z - 4*d**2*m*s*v*z**2 + 2*d**2*m*s*w*z**2 + 2*d**2*m*s*y*z**2 - 4*d**2*n*p**2*s*w + 4*d**2*n*p*s**2*v - 4*d**2*n*p*s**2*w + 8*d**2*n*p*s*v*z - 8*d**2*n*p*s*w*z + 8*d**2*n*s**2*v*z - 4*d**2*n*s**2*w*z - 4*d**2*n*s**2*y*z + 8*d**2*n*s*v*z**2 - 4*d**2*n*s*w*z**2 - 4*d**2*n*s*y*z**2 + 2*d**2*o*p**2*s*w - 2*d**2*o*p*s**2*v + 2*d**2*o*p*s**2*w - 4*d**2*o*p*s*v*z + 4*d**2*o*p*s*w*z - 4*d**2*o*s**2*v*z + 2*d**2*o*s**2*w*z + 2*d**2*o*s**2*y*z - 4*d**2*o*s*v*z**2 + 2*d**2*o*s*w*z**2 + 2*d**2*o*s*y*z**2 + 4*d**2*p**2*q*s*x - 2*d**2*p**2*r*s*x + 4*d**2*p*q*s**2*x + 8*d**2*p*q*s*x*z - 2*d**2*p*r*s**2*x - 4*d**2*p*r*s*x*z + 4*d**2*q*s**2*u*z + 4*d**2*q*s**2*x*z + 4*d**2*q*s*u*z**2 + 4*d**2*q*s*x*z**2 - 2*d**2*r*s**2*u*z - 2*d**2*r*s**2*x*z - 2*d**2*r*s*u*z**2 - 2*d**2*r*s*x*z**2 + 6*d*f*g*p**2*s**2 - 6*d*f*h*p**2*s**2 - 18*d*g*p**2*q*s**2 + 12*d*g*p**2*r*s**2 + 24*d*h*p**2*q*s**2 - 18*d*h*p**2*r*s**2 - 6*d*l*p**2*q*s**2 + 6*d*l*p**2*r*s**2 + 4*f*g*p**2*s**3 - 8*f*h*p**2*s**3 + 4*f*l*p**2*s**3 - 8*g*p**2*q*s**3 + 4*g*p**2*r*s**3 + 16*h*p**2*q*s**3 - 8*h*p**2*r*s**3 - 8*l*p**2*q*s**3 + 4*l*p**2*r*s**3 ) / (d**4*p**2)
    a2 = (+2*a*d**4*k - a*d**4*u - a*d**4*x + 4*a*d**3*k*p + 4*a*d**3*k*s + 8*a*d**3*k*z - 4*a*d**3*p*x - 2*a*d**3*s*u - 2*a*d**3*s*x - 4*a*d**3*u*z - 4*a*d**3*x*z + 4*a*d**2*k*p*s + 2*a*d**2*k*p*z + 2*a*d**2*k*s**2 + 8*a*d**2*k*s*z + 2*a*d**2*k*z**2 + 6*a*d**2*m*p**2 - 6*a*d**2*n*p**2 + a*d**2*o*p**2 - a*d**2*p**2*x - 4*a*d**2*p*s*x - 2*a*d**2*p*x*z - a*d**2*s**2*u - a*d**2*s**2*x - 4*a*d**2*s*u*z - 4*a*d**2*s*x*z - a*d**2*u*z**2 - a*d**2*x*z**2 + 12*a*d*m*p**2*s - 18*a*d*n*p**2*s + 6*a*d*o*p**2*s + 6*a*m*p**2*s**2 - 12*a*n*p**2*s**2 + 6*a*o*p**2*s**2 - 4*b*d**3*k*p - 4*b*d**3*k*s - 8*b*d**3*k*z + 4*b*d**3*p*x + 2*b*d**3*s*u + 2*b*d**3*s*x + 4*b*d**3*u*z + 4*b*d**3*x*z - 8*b*d**2*k*p*s - 4*b*d**2*k*p*z - 4*b*d**2*k*s**2 - 16*b*d**2*k*s*z - 4*b*d**2*k*z**2 - 6*b*d**2*m*p**2 + 4*b*d**2*n*p**2 + 2*b*d**2*p**2*x + 8*b*d**2*p*s*x + 4*b*d**2*p*x*z + 2*b*d**2*s**2*u + 2*b*d**2*s**2*x + 8*b*d**2*s*u*z + 8*b*d**2*s*x*z + 2*b*d**2*u*z**2 + 2*b*d**2*x*z**2 - 18*b*d*m*p**2*s + 24*b*d*n*p**2*s - 6*b*d*o*p**2*s - 12*b*m*p**2*s**2 + 24*b*n*p**2*s**2 - 12*b*o*p**2*s**2 + 4*c*d**2*k*p*s + 2*c*d**2*k*p*z + 2*c*d**2*k*s**2 + 8*c*d**2*k*s*z + 2*c*d**2*k*z**2 + c*d**2*m*p**2 - c*d**2*p**2*x - 4*c*d**2*p*s*x - 2*c*d**2*p*x*z - c*d**2*s**2*u - c*d**2*s**2*x - 4*c*d**2*s*u*z - 4*c*d**2*s*x*z - c*d**2*u*z**2 - c*d**2*x*z**2 + 6*c*d*m*p**2*s - 6*c*d*n*p**2*s + 6*c*m*p**2*s**2 - 12*c*n*p**2*s**2 + 6*c*o*p**2*s**2 - 2*d**4*g*v + d**4*g*w + d**4*g*y - 2*d**4*k*r + 2*d**4*m*v - d**4*m*w - d**4*m*y + d**4*r*u + d**4*r*x - 4*d**3*g*p*v + 4*d**3*g*p*w - 4*d**3*g*s*v + 2*d**3*g*s*w + 2*d**3*g*s*y - 8*d**3*g*v*z + 4*d**3*g*w*z + 4*d**3*g*y*z + 4*d**3*h*p*v - 4*d**3*h*p*w + 4*d**3*h*s*v - 2*d**3*h*s*w - 2*d**3*h*s*y + 8*d**3*h*v*z - 4*d**3*h*w*z - 4*d**3*h*y*z + 4*d**3*k*p*q - 4*d**3*k*p*r + 4*d**3*k*q*s + 8*d**3*k*q*z - 4*d**3*k*r*s - 8*d**3*k*r*z + 4*d**3*m*p*v - 4*d**3*m*p*w + 4*d**3*m*s*v - 2*d**3*m*s*w - 2*d**3*m*s*y + 8*d**3*m*v*z - 4*d**3*m*w*z - 4*d**3*m*y*z - 4*d**3*n*p*v + 4*d**3*n*p*w - 4*d**3*n*s*v + 2*d**3*n*s*w + 2*d**3*n*s*y - 8*d**3*n*v*z + 4*d**3*n*w*z + 4*d**3*n*y*z - 4*d**3*p*q*x + 4*d**3*p*r*x - 2*d**3*q*s*u - 2*d**3*q*s*x - 4*d**3*q*u*z - 4*d**3*q*x*z + 2*d**3*r*s*u + 2*d**3*r*s*x + 4*d**3*r*u*z + 4*d**3*r*x*z - d**2*f*g*p**2 - 4*d**2*f*k*p*s - 2*d**2*f*k*p*z - 2*d**2*f*k*s**2 - 8*d**2*f*k*s*z - 2*d**2*f*k*z**2 + d**2*f*p**2*x + 4*d**2*f*p*s*x + 2*d**2*f*p*x*z + d**2*f*s**2*u + d**2*f*s**2*x + 4*d**2*f*s*u*z + 4*d**2*f*s*x*z + d**2*f*u*z**2 + d**2*f*x*z**2 + 6*d**2*g*p**2*q - 6*d**2*g*p**2*r + d**2*g*p**2*w - 4*d**2*g*p*s*v + 4*d**2*g*p*s*w - 2*d**2*g*p*v*z + 2*d**2*g*p*w*z - 2*d**2*g*s**2*v + d**2*g*s**2*w + d**2*g*s**2*y - 8*d**2*g*s*v*z + 4*d**2*g*s*w*z + 4*d**2*g*s*y*z - 2*d**2*g*v*z**2 + d**2*g*w*z**2 + d**2*g*y*z**2 - 4*d**2*h*p**2*q + 6*d**2*h*p**2*r - 2*d**2*h*p**2*w + 8*d**2*h*p*s*v - 8*d**2*h*p*s*w + 4*d**2*h*p*v*z - 4*d**2*h*p*w*z + 4*d**2*h*s**2*v - 2*d**2*h*s**2*w - 2*d**2*h*s**2*y + 16*d**2*h*s*v*z - 8*d**2*h*s*w*z - 8*d**2*h*s*y*z + 4*d**2*h*v*z**2 - 2*d**2*h*w*z**2 - 2*d**2*h*y*z**2 + 8*d**2*k*p*q*s + 4*d**2*k*p*q*z - 4*d**2*k*p*r*s - 2*d**2*k*p*r*z + 4*d**2*k*q*s**2 + 16*d**2*k*q*s*z + 4*d**2*k*q*z**2 - 2*d**2*k*r*s**2 - 8*d**2*k*r*s*z - 2*d**2*k*r*z**2 - d**2*l*p**2*r + d**2*l*p**2*w - 4*d**2*l*p*s*v + 4*d**2*l*p*s*w - 2*d**2*l*p*v*z + 2*d**2*l*p*w*z - 2*d**2*l*s**2*v + d**2*l*s**2*w + d**2*l*s**2*y - 8*d**2*l*s*v*z + 4*d**2*l*s*w*z + 4*d**2*l*s*y*z - 2*d**2*l*v*z**2 + d**2*l*w*z**2 + d**2*l*y*z**2 - d**2*m*p**2*w + 4*d**2*m*p*s*v - 4*d**2*m*p*s*w + 2*d**2*m*p*v*z - 2*d**2*m*p*w*z + 2*d**2*m*s**2*v - d**2*m*s**2*w - d**2*m*s**2*y + 8*d**2*m*s*v*z - 4*d**2*m*s*w*z - 4*d**2*m*s*y*z + 2*d**2*m*v*z**2 - d**2*m*w*z**2 - d**2*m*y*z**2 + 2*d**2*n*p**2*w - 8*d**2*n*p*s*v + 8*d**2*n*p*s*w - 4*d**2*n*p*v*z + 4*d**2*n*p*w*z - 4*d**2*n*s**2*v + 2*d**2*n*s**2*w + 2*d**2*n*s**2*y - 16*d**2*n*s*v*z + 8*d**2*n*s*w*z + 8*d**2*n*s*y*z - 4*d**2*n*v*z**2 + 2*d**2*n*w*z**2 + 2*d**2*n*y*z**2 - d**2*o*p**2*w + 4*d**2*o*p*s*v - 4*d**2*o*p*s*w + 2*d**2*o*p*v*z - 2*d**2*o*p*w*z + 2*d**2*o*s**2*v - d**2*o*s**2*w - d**2*o*s**2*y + 8*d**2*o*s*v*z - 4*d**2*o*s*w*z - 4*d**2*o*s*y*z + 2*d**2*o*v*z**2 - d**2*o*w*z**2 - d**2*o*y*z**2 - 2*d**2*p**2*q*x + d**2*p**2*r*x - 8*d**2*p*q*s*x - 4*d**2*p*q*x*z + 4*d**2*p*r*s*x + 2*d**2*p*r*x*z - 2*d**2*q*s**2*u - 2*d**2*q*s**2*x - 8*d**2*q*s*u*z - 8*d**2*q*s*x*z - 2*d**2*q*u*z**2 - 2*d**2*q*x*z**2 + d**2*r*s**2*u + d**2*r*s**2*x + 4*d**2*r*s*u*z + 4*d**2*r*s*x*z + d**2*r*u*z**2 + d**2*r*x*z**2 - 6*d*f*g*p**2*s + 6*d*f*h*p**2*s + 18*d*g*p**2*q*s - 12*d*g*p**2*r*s - 24*d*h*p**2*q*s + 18*d*h*p**2*r*s + 6*d*l*p**2*q*s - 6*d*l*p**2*r*s - 6*f*g*p**2*s**2 + 12*f*h*p**2*s**2 - 6*f*l*p**2*s**2 + 12*g*p**2*q*s**2 - 6*g*p**2*r*s**2 - 24*h*p**2*q*s**2 + 12*h*p**2*r*s**2 + 12*l*p**2*q*s**2 - 6*l*p**2*r*s**2 ) / (d**4*p**2)
    a3 = (-4*a*d**3*k + 2*a*d**3*u + 2*a*d**3*x - 2*a*d**2*k*p - 4*a*d**2*k*s - 4*a*d**2*k*z + 2*a*d**2*p*x + 2*a*d**2*s*u + 2*a*d**2*s*x + 2*a*d**2*u*z + 2*a*d**2*x*z - 4*a*d*m*p**2 + 6*a*d*n*p**2 - 2*a*d*o*p**2 - 4*a*m*p**2*s + 8*a*n*p**2*s - 4*a*o*p**2*s + 4*b*d**3*k - 2*b*d**3*u - 2*b*d**3*x + 4*b*d**2*k*p + 8*b*d**2*k*s + 8*b*d**2*k*z - 4*b*d**2*p*x - 4*b*d**2*s*u - 4*b*d**2*s*x - 4*b*d**2*u*z - 4*b*d**2*x*z + 6*b*d*m*p**2 - 8*b*d*n*p**2 + 2*b*d*o*p**2 + 8*b*m*p**2*s - 16*b*n*p**2*s + 8*b*o*p**2*s - 2*c*d**2*k*p - 4*c*d**2*k*s - 4*c*d**2*k*z + 2*c*d**2*p*x + 2*c*d**2*s*u + 2*c*d**2*s*x + 2*c*d**2*u*z + 2*c*d**2*x*z - 2*c*d*m*p**2 + 2*c*d*n*p**2 - 4*c*m*p**2*s + 8*c*n*p**2*s - 4*c*o*p**2*s + 4*d**3*g*v - 2*d**3*g*w - 2*d**3*g*y - 4*d**3*h*v + 2*d**3*h*w + 2*d**3*h*y - 4*d**3*k*q + 4*d**3*k*r - 4*d**3*m*v + 2*d**3*m*w + 2*d**3*m*y + 4*d**3*n*v - 2*d**3*n*w - 2*d**3*n*y + 2*d**3*q*u + 2*d**3*q*x - 2*d**3*r*u - 2*d**3*r*x + 2*d**2*f*k*p + 4*d**2*f*k*s + 4*d**2*f*k*z - 2*d**2*f*p*x - 2*d**2*f*s*u - 2*d**2*f*s*x - 2*d**2*f*u*z - 2*d**2*f*x*z + 2*d**2*g*p*v - 2*d**2*g*p*w + 4*d**2*g*s*v - 2*d**2*g*s*w - 2*d**2*g*s*y + 4*d**2*g*v*z - 2*d**2*g*w*z - 2*d**2*g*y*z - 4*d**2*h*p*v + 4*d**2*h*p*w - 8*d**2*h*s*v + 4*d**2*h*s*w + 4*d**2*h*s*y - 8*d**2*h*v*z + 4*d**2*h*w*z + 4*d**2*h*y*z - 4*d**2*k*p*q + 2*d**2*k*p*r - 8*d**2*k*q*s - 8*d**2*k*q*z + 4*d**2*k*r*s + 4*d**2*k*r*z + 2*d**2*l*p*v - 2*d**2*l*p*w + 4*d**2*l*s*v - 2*d**2*l*s*w - 2*d**2*l*s*y + 4*d**2*l*v*z - 2*d**2*l*w*z - 2*d**2*l*y*z - 2*d**2*m*p*v + 2*d**2*m*p*w - 4*d**2*m*s*v + 2*d**2*m*s*w + 2*d**2*m*s*y - 4*d**2*m*v*z + 2*d**2*m*w*z + 2*d**2*m*y*z + 4*d**2*n*p*v - 4*d**2*n*p*w + 8*d**2*n*s*v - 4*d**2*n*s*w - 4*d**2*n*s*y + 8*d**2*n*v*z - 4*d**2*n*w*z - 4*d**2*n*y*z - 2*d**2*o*p*v + 2*d**2*o*p*w - 4*d**2*o*s*v + 2*d**2*o*s*w + 2*d**2*o*s*y - 4*d**2*o*v*z + 2*d**2*o*w*z + 2*d**2*o*y*z + 4*d**2*p*q*x - 2*d**2*p*r*x + 4*d**2*q*s*u + 4*d**2*q*s*x + 4*d**2*q*u*z + 4*d**2*q*x*z - 2*d**2*r*s*u - 2*d**2*r*s*x - 2*d**2*r*u*z - 2*d**2*r*x*z + 2*d*f*g*p**2 - 2*d*f*h*p**2 - 6*d*g*p**2*q + 4*d*g*p**2*r + 8*d*h*p**2*q - 6*d*h*p**2*r - 2*d*l*p**2*q + 2*d*l*p**2*r + 4*f*g*p**2*s - 8*f*h*p**2*s + 4*f*l*p**2*s - 8*g*p**2*q*s + 4*g*p**2*r*s + 16*h*p**2*q*s - 8*h*p**2*r*s - 8*l*p**2*q*s + 4*l*p**2*r*s ) / (d**4*p**2)
    a4 = (+2*a*d**2*k - a*d**2*u - a*d**2*x + a*m*p**2 - 2*a*n*p**2 + a*o*p**2 - 4*b*d**2*k + 2*b*d**2*u + 2*b*d**2*x - 2*b*m*p**2 + 4*b*n*p**2 - 2*b*o*p**2 + 2*c*d**2*k - c*d**2*u - c*d**2*x + c*m*p**2 - 2*c*n*p**2 + c*o*p**2 - 2*d**2*f*k + d**2*f*u + d**2*f*x - 2*d**2*g*v + d**2*g*w + d**2*g*y + 4*d**2*h*v - 2*d**2*h*w - 2*d**2*h*y + 4*d**2*k*q - 2*d**2*k*r - 2*d**2*l*v + d**2*l*w + d**2*l*y + 2*d**2*m*v - d**2*m*w - d**2*m*y - 4*d**2*n*v + 2*d**2*n*w + 2*d**2*n*y + 2*d**2*o*v - d**2*o*w - d**2*o*y - 2*d**2*q*u - 2*d**2*q*x + d**2*r*u + d**2*r*x - f*g*p**2 + 2*f*h*p**2 - f*l*p**2 + 2*g*p**2*q - g*p**2*r - 4*h*p**2*q + 2*h*p**2*r + 2*l*p**2*q - l*p**2*r ) / (d**4*p**2)

    coeff = [a4]
    coeff += [a3]
    coeff += [a2]
    coeff += [a1]
    coeff += [a0]

    r = np.roots(coeff)
    e_exec_time = time.time()

    solver_exec_time = e_exec_time - s_exec_time

    # I believe that the result may contain only real solutions since the domain is (explicitly) real?
    #r = [re(_r) for _r in r if im(_r) == 0 and _r >= 0 and _r <= 1]
    r = [re(_r) for _r in r if im(_r) == 0]
    r.sort()

    N = len(r)
    K = 0

    while K < N:
        if r[K] >= it.x - eps and r[K] <= it.x + eps:
            r[K] = it.x
        elif r[K] >= it.y - eps and r[K] <= it.y + eps:
            r[K] = it.y

        K += 1

    K = 0
    _r = []

    while K < N:
        if r[K] >= it.x and r[K] <= it.y:
            _r += [r[K]]

        K += 1

    r = _r

    return solver_exec_time, r

def get_solutions_quad(a0, a1, a2):
    global eps

    s_exec_time = time.time()

    """
    a0 = (-d**2*k*m + d**2*k*y - d**2*v*z - 2*d*k*m*s + 2*d*k*n*s - k*m*s**2 + 2*k*n*s**2 - k*o*s**2) / (d**2*k)
    a1 = (+d**2*z + 2*d*k*m - 2*d*k*n + 2*k*m*s - 4*k*n*s + 2*k*o*s) / (d**2*k)
    a2 = (-k*m + 2*k*n - k*o) / (d**2*k)
    """

    #a3 = (-a*d**2*z - 4*a*d*k*m + 6*a*d*k*n - 2*a*d*k*o - 4*a*k*m*s + 8*a*k*n*s - 4*a*k*o*s + 2*b*d**2*z + 6*b*d*k*m - 8*b*d*k*n + 2*b*d*k*o + 8*b*k*m*s - 16*b*k*n*s + 8*b*k*o*s - c*d**2*z - 2*c*d*k*m + 2*c*d*k*n - 4*c*k*m*s + 8*c*k*n*s - 4*c*k*o*s + d**2*f*z + d**2*g*w - 2*d**2*h*w + d**2*l*w - d**2*m*w + 2*d**2*n*w - d**2*o*w - 2*d**2*q*z + d**2*r*z + 2*d*f*g*k - 2*d*f*h*k - 6*d*g*k*q + 4*d*g*k*r + 8*d*h*k*q - 6*d*h*k*r - 2*d*k*l*q + 2*d*k*l*r + 4*f*g*k*s - 8*f*h*k*s + 4*f*k*l*s - 8*g*k*q*s + 4*g*k*r*s + 16*h*k*q*s - 8*h*k*r*s - 8*k*l*q*s + 4*k*l*r*s ) / (d**4*k)
    #a4 = (a*k*m - 2*a*k*n + a*k*o - 2*b*k*m + 4*b*k*n - 2*b*k*o + c*k*m - 2*c*k*n + c*k*o - f*g*k + 2*f*h*k - f*k*l + 2*g*k*q - g*k*r - 4*h*k*q + 2*h*k*r + 2*k*l*q - k*l*r ) / (d**4*k)

    #coeff = [a4]
    #coeff += [a3]

    # calculate the discriminant
    det = (a1**2) - (4*a2*a0)

    # Has no real roots
    if det < 0:
        e_exec_time = time.time()
        solver_exec_time = e_exec_time - s_exec_time
        return solver_exec_time, []

    r = []
    if det == 0:
        r1 = (-a1 - cmath.sqrt(det)) / (2*a2)

        r += [r1]
    else:
        r1 = (-a1 - cmath.sqrt(det)) / (2*a2)
        r2 = (-a1 + cmath.sqrt(det)) / (2*a2)

        if r1 < r2:
            r += [r1]
            r += [r2]
        else:
            r += [r2]
            r += [r1]

    """
    coeff = [a2]
    coeff += [a1]
    coeff += [a0]

    r = np.roots(coeff)
    """

    e_exec_time = time.time()
    solver_exec_time = e_exec_time - s_exec_time

    #r = [re(_r) for _r in r if im(_r) == 0]
    r.sort()

    N = len(r)
    K = 0

    while K < N:
        if r[K] >= it.x - eps and r[K] <= it.x + eps:
            r[K] = it.x
        elif r[K] >= it.y - eps and r[K] <= it.y + eps:
            r[K] = it.y

        K += 1

    K = 0
    _r = []

    while K < N:
        if r[K] >= it.x and r[K] <= it.y:
            _r += [r[K]]

        K += 1

    r = _r

    return solver_exec_time, r

#-------------------------------------------------------------------
# Get the intersection times between a moving seg and a moving point
#-------------------------------------------------------------------
def get_intersection_times(ms, mp, i):
    global solver_exec_time
    global solver_exec_times
    global epsilon
    #global coll

    s = []
    t = Symbol('t')
    idxms = 0
    idxmp = 0
    end = 0

    while idxms < len(ms.units) and idxmp < len(mp.units):
        msu = ms.units[idxms]
        mpu = mp.units[idxmp]

        if msu.i.x >= i.y or mpu.i.x >= i.y:
            break

        #print(msu.i.to_string())
        it0 = msu.i.intersection(i)
        #print(it0.to_string())
        if it0 is None:
            idxms += 1
            continue

        it1 = mpu.i.intersection(i)
        if it1 is None:
            idxmp += 1
            continue

        it = it0.intersection(it1)
        #print(it.to_string())
        if it != None:
            idx = 0
            n = len(msu.c0.intervals)

            while idx < n:
                it0 = msu.c0.intervals[idx].intersection(it)
                if it0 is None:
                    idx += 1
                    continue

                col = collinear(msu.c0.curves[idx].cp0, msu.c0.curves[idx].cp1, msu.c0.curves[idx].cp2, msu.c1.curves[idx].cp0, msu.c1.curves[idx].cp1, msu.c1.curves[idx].cp2, mpu.p[0], mpu.p[1])

                dt = msu.c0.intervals[idx].y - msu.c0.intervals[idx].x
                T = (t - msu.c0.intervals[idx].x) / dt
                
                Ax, Ay = msu.c0.curves[idx].at(T)
                Bx, By = msu.c1.curves[idx].at(T)

                dt = mpu.i.y - mpu.i.x
                T = (t - mpu.i.x) / dt
                Cx, Cy = mpu.at(T)

                done = False

                if col == 0:
                    """
                    if coll:
                        #print('0')
                        n = len(s)
                        #s[len(s) - 1] = Interval(s[len(s) - 1], end, True, True)
                        prev = s[n-1]
                        if isinstance(prev, Interval):
                            prev.y = end
                        else:
                            s[n-1] = Interval(prev, end, True, True)

                        coll = False
                    """
                    #print('<>')
                    f = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By)
                    exec_time, r = get_solutions(f, t, it0)

                    solver_exec_time += exec_time
                    solver_exec_times += 1
                else:
                    """
                    if coll:
                        n = len(s)
                        #print('1')
                        #s[len(s) - 1] = Interval(s[len(s) - 1], end, True, True)
                        prev = s[n-1]
                        if isinstance(prev, Interval):
                            prev.y = end
                        else:
                            s[n-1] = Interval(prev, end, True, True)
                    """

                    ###

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
                        if col == 1:
                            f = Cy - By
                        else:
                            f = Cx - Bx

                        exec_time, r = get_solutions(f, t, it0)

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
                        if col == 1:
                            f = Cy - Ay
                        else:
                            f = Cx - Ax

                        exec_time, r0 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        if col == 1:
                            f = Cy - By
                        else:
                            f = Cx - Bx

                        exec_time, r1 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        r = r0 + r1

                if not done:
                    r.sort()

                    inc = 0
                    a = None
                    b = None

                    for root in r:
                        Px, Py = mp.at(root)
                        Ax, Ay, Bx, By = msu.at(root)

                        # Is point on the segment?
                        if (min(Ax, Bx) - epsilon <= Px and Px <= max(Ax, Bx) + epsilon) and (min(Ay, By) - epsilon <= Py and Py <= max(Ay, By) + epsilon):
                            inc += 1
                            n = len(s)

                            if col != 0:
                                if inc == 1:
                                    a = root
                                else:
                                    b = root
                            else:

                                """
                                if coll and inc == 2:
                                    #print('2')
                                    prev = s[n-1]
                                    if isinstance(prev, Interval):
                                        #prev = Interval(prev.x, root, True, True)
                                        prev.y = root
                                    else:
                                        s[n-1] = Interval(prev, root, True, True)
                                else:
                                """

                                if n == 0:
                                    s += [root]
                                else:
                                    prev = s[n-1]

                                    if isinstance(prev, Interval):
                                        if not prev.contains(root):
                                            s += [root]
                                    else:
                                        if root != prev:
                                            s += [root]

                    if col != 0:
                        n = len(s)

                        if a != None and b != None:
                            if n == 0:
                                s += [Interval(a, b, True, True)]
                            else:
                                prev = s[n-1]

                                if isinstance(prev, Interval):
                                    if not prev.contains(a):
                                        s += [Interval(a, b, True, True)]
                                    else:
                                        prev.y = b
                                else:
                                    if a != prev:
                                        s += [Interval(a, b, True, True)]
                                    else:
	                                    s[n-1] = Interval(a, b, True, True)
                        elif a != None and b == None:
                            if n == 0:
                                if a == it0.y:
                                    s += [a]
                                else:
                                    s += [Interval(a, it0.y, True, True)]
                            else:
                                prev = s[n-1]

                                if isinstance(prev, Interval):
                                    if not prev.contains(a):
                                        if a == it0.y:
                                            s += [a]
                                        else:
                                            s += [Interval(a, it0.y, True, True)]
                                    else:
                                        if a < it0.y and prev.y < it0.y:
                                            prev.y = it0.y
                                else:
                                    if a != prev:
                                        if a == it0.y:
                                            s += [a]
                                        else:
                                            s += [Interval(a, it0.y, True, True)]
                                        #s += [Interval(a, it0.y, True, True)]
                                    else:
                                        if a < it0.y:
	                                        s[n-1] = Interval(a, it0.y, True, True)

                    #if coll and inc == 2:
                    #    coll = False

                idx += 1

        # Next unit(s).
        if msu.i.y == mpu.i.y:
            idxms += 1
            idxmp += 1
        elif msu.i.y < mpu.i.y:
            idxms += 1
        else:
            idxmp += 1

    """
    if coll:
        n = len(s)
        prev = s[n-1]
        if isinstance(prev, Interval):
            prev.y = end
        else:
            if prev != end:
                s[n-1] = Interval(prev, end, True, True)
        #pass
        #s[len(s) - 1] = Interval(s[len(s) - 1], end, True, True)
    """
    return s

#-------------------------------------------------------------------
# Get the intersection times between a moving seg and a moving point
# If prev != None > will sort prev and the new list of intersections
#-------------------------------------------------------------------
def get_intersections(ms, mp, i, prev = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon
    #global coll

    s = []
    t = Symbol('t')
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

                col = collinear(msu.c0.curves[idx].cp0, msu.c0.curves[idx].cp1, msu.c0.curves[idx].cp2, msu.c1.curves[idx].cp0, msu.c1.curves[idx].cp1, msu.c1.curves[idx].cp2, mpu.p[0], mpu.p[1])
                #print(col)
                dt = msu.c0.intervals[idx].y - msu.c0.intervals[idx].x
                T = (t - msu.c0.intervals[idx].x) / dt

                d = dt
                ix = msu.c0.intervals[idx].x
                a = msu.c0.curves[idx].cp0.x
                b = msu.c0.curves[idx].cp1.x
                c = msu.c0.curves[idx].cp2.x

                g = msu.c0.curves[idx].cp0.y
                h = msu.c0.curves[idx].cp1.y
                l = msu.c0.curves[idx].cp2.y

                r = msu.c1.curves[idx].cp0.x
                q = msu.c1.curves[idx].cp1.x
                f = msu.c1.curves[idx].cp2.x

                m = msu.c1.curves[idx].cp0.y
                _n = msu.c1.curves[idx].cp1.y
                o = msu.c1.curves[idx].cp2.y

                Ax, Ay = msu.c0.curves[idx].at(T)
                Bx, By = msu.c1.curves[idx].at(T)

                dt = mpu.i.y - mpu.i.x
                T = (t - mpu.i.x) / dt
                Cx, Cy = mpu.at(T)

                v = mpu.i.x
                k = dt
                x = mpu.p[0].x
                y = mpu.p[0].y
                w = mpu.p[1].x - mpu.p[0].x
                z = mpu.p[1].y - mpu.p[0].y

                #a((T - ix)/dt)^2 - 2a((T - ix)/dt) + a + 2b((T - ix)/dt) - 2b((T - ix)/dt)^2 + c((T - ix)/dt)^2 - y + dy((T - ixx)/dtt)
                #a((T - i)/d)^2 - 2a((T - i)/d) + a + 2b((T - i)/d) - 2b((T - i)/d)^2 + c((T - i)/d)^2 - y + z((T - x)/v)
                """
                Ax = A*((T-s)/d)^2 - 2*A*((T-s)/d) + A + 2*B*((T-s)/d) - 2*B*((T-s)/d)^2 + C*((T-s)/d)^2
				Bx = R*((T-s)/d)^2 - 2*R*((T-s)/d) + R + 2*Q*((T-s)/d) - 2*Q*((T-s)/d)^2 + F*((T-s)/d)^2
                Ay = G*((T-s)/d)^2 - 2*G*((T-s)/d) + G + 2*H*((T-s)/d) - 2*H*((T-s)/d)^2 + L*((T-s)/d)^2
				By = M*((T-s)/d)^2 - 2*M*((T-s)/d) + M + 2*N*((T-s)/d) - 2*N*((T-s)/d)^2 + O*((T-s)/d)^2
                Cx = x + w*((T-v)/k)
                Cy = y + z*((T-v)/k)

                f = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By)

                (A*((T-s)/d)^2 - 2*A*((T-s)/d) + A + 2*B*((T-s)/d) - 2*B*((T-s)/d)^2 + C*((T-s)/d)^2) * ((M*((T-s)/d)^2 - 2*M*((T-s)/d) + M + 2*N*((T-s)/d) - 2*N*((T-s)/d)^2 + O*((T-s)/d)^2) - (y + z*((T-v)/k))) + (R*((T-s)/d)^2 - 2*R*((T-s)/d) + R + 2*Q*((T-s)/d) - 2*Q*((T-s)/d)^2 + F*((T-s)/d)^2) * ((y + z*((T-v)/k)) - (G*((T-s)/d)^2 - 2*G*((T-s)/d) + G + 2*H*((T-s)/d) - 2*H*((T-s)/d)^2 + L*((T-s)/d)^2)) + (x + w*((T-v)/k)) * ((G*((T-s)/d)^2 - 2*G*((T-s)/d) + G + 2*H*((T-s)/d) - 2*H*((T-s)/d)^2 + L*((T-s)/d)^2) - (M*((T-s)/d)^2 - 2*M*((T-s)/d) + M + 2*N*((T-s)/d) - 2*N*((T-s)/d)^2 + O*((T-s)/d)^2))

                # https://www.mathpapa.com/simplify-calculator/

				(ad^4fz + ad^4km - ad^4ky - ad^4tz + 2ad^3fsz - 2ad^3ftz + 4ad^3kms - 4ad^3kmt - 2ad^3kns + 2ad^3knt - 2ad^3ksy + 2ad^3kty - 2ad^3stz + 2ad^3t^2z + ad^2fs^2z - 2ad^2fstz + ad^2ft^2z + 6ad^2kms^2 - 12ad^2kmst + 6ad^2kmt^2 - 6ad^2kns^2 + 12ad^2knst - 6ad^2knt^2 + ad^2kos^2 - 2ad^2kost + ad^2kot^2 - ad^2ks^2y + 2ad^2ksty - ad^2kt^2y - ad^2s^2tz + 2ad^2st^2z - ad^2t^3z + 4adkms^3 - 12adkms^2t + 12adkmst^2 - 4adkmt^3 - 6adkns^3 + 18adkns^2t - 18adknst^2 + 6adknt^3 + 2adkos^3 - 6adkos^2t + 6adkost^2 - 2adkot^3 + akms^4 - 4akms^3t + 6akms^2t^2 - 4akmst^3 + akmt^4 - 2akns^4 + 8akns^3t - 12akns^2t^2 + 8aknst^3 - 2aknt^4 + akos^4 - 4akos^3t + 6akos^2t^2 - 4akost^3 + akot^4 - 2bd^3fsz + 2bd^3ftz - 2bd^3kms + 2bd^3kmt + 2bd^3ksy - 2bd^3kty + 2bd^3stz - 2bd^3t^2z - 2bd^2fs^2z + 4bd^2fstz - 2bd^2ft^2z - 6bd^2kms^2 + 12bd^2kmst - 6bd^2kmt^2 + 4bd^2kns^2 - 8bd^2knst + 4bd^2knt^2 + 2bd^2ks^2y - 4bd^2ksty + 2bd^2kt^2y + 2bd^2s^2tz - 4bd^2st^2z + 2bd^2t^3z - 6bdkms^3 + 18bdkms^2t - 18bdkmst^2 + 6bdkmt^3 + 8bdkns^3 - 24bdkns^2t + 24bdknst^2 - 8bdknt^3 - 2bdkos^3 + 6bdkos^2t - 6bdkost^2 + 2bdkot^3 - 2bkms^4 + 8bkms^3t - 12bkms^2t^2 + 8bkmst^3 - 2bkmt^4 + 4bkns^4 - 16bkns^3t + 24bkns^2t^2 - 16bknst^3 + 4bknt^4 - 2bkos^4 + 8bkos^3t - 12bkos^2t^2 + 8bkost^3 - 2bkot^4 + cd^2fs^2z - 2cd^2fstz + cd^2ft^2z + cd^2kms^2 - 2cd^2kmst + cd^2kmt^2 - cd^2ks^2y + 2cd^2ksty - cd^2kt^2y - cd^2s^2tz + 2cd^2st^2z - cd^2t^3z + 2cdkms^3 - 6cdkms^2t + 6cdkmst^2 - 2cdkmt^3 - 2cdkns^3 + 6cdkns^2t - 6cdknst^2 + 2cdknt^3 + ckms^4 - 4ckms^3t + 6ckms^2t^2 - 4ckmst^3 + ckmt^4 - 2ckns^4 + 8ckns^3t - 12ckns^2t^2 + 8cknst^3 - 2cknt^4 + ckos^4 - 4ckos^3t + 6ckos^2t^2 - 4ckost^3 + ckot^4 - d^5fz - d^5gk + d^5ky + d^5tz - d^4fgw + d^4fmw - 2d^4fsz + 2d^4ftz - 4d^4gks +4d^4gkt + d^4gkx + d^4gtw + 2d^4hks - 2d^4hkt - d^4kmx + 2d^4ksy - 2d^4kty - d^4mtw + 2d^4stz - 2d^4t^2z - 2d^3fgsw + 2d^3fgtw + 2d^3fhsw - 2d^3fhtw + 2d^3fmsw - 2d^3fmtw - 2d^3fnsw + 2d^3fntw + 2d^3fqsz - 2d^3fqtz - d^3fs^2z + 2d^3fstz - d^3ft^2z + 2d^3gkqs - 2d^3gkqt - 6d^3gks^2 + 12d^3gkst + 2d^3gksx - 6d^3gkt^2 - 2d^3gktx + 2d^3gstw - 2d^3gt^2w + 6d^3hks^2 - 12d^3hkst - 2d^3hksx + 6d^3hkt^2 + 2d^3hktx - 2d^3hstw + 2d^3ht^2w - d^3kls^2 + 2d^3klst - d^3klt^2 - 2d^3kmsx + 2d^3kmtx + 2d^3knsx - 2d^3kntx - 2d^3kqsy + 2d^3kqty + d^3ks^2y - 2d^3ksty + d^3kt^2y - 2d^3mstw + 2d^3mt^2w +2d^3nstw - 2d^3nt^2w - 2d^3qstz + 2d^3qt^2z + d^3s^2tz - 2d^3st^2z + d^3t^3z - d^2f^2s^2z + 2d^2f^2stz - d^2f^2t^2z - d^2fgks^2 + 2d^2fgkst - d^2fgkt^2 - d^2fgs^2w + 2d^2fgstw - d^2fgt^2w + 2d^2fhs^2w - 4d^2fhstw + 2d^2fht^2w + d^2fks^2y - 2d^2fksty + d^2fkt^2y - d^2fls^2w + 2d^2flstw - d^2flt^2w + d^2fms^2w - 2d^2fmstw + d^2fmt^2w - 2d^2fns^2w + 4d^2fnstw - 2d^2fnt^2w + d^2fos^2w - 2d^2fostw + d^2fot^2w + 2d^2fqs^2z - 4d^2fqstz + 2d^2fqt^2z + d^2fs^2tz - 2d^2fst^2z + d^2ft^3z + 6d^2gkqs^2 - 12d^2gkqst + 6d^2gkqt^2 - 4d^2gks^3 + 12d^2gks^2t + d^2gks^2x - 12d^2gkst^2 - 2d^2gkstx + 4d^2gkt^3 + d^2gkt^2x + d^2gs^2tw - 2d^2gst^2w + d^2gt^3w - 4d^2hkqs^2 + 8d^2hkqst - 4d^2hkqt^2 + 6d^2hks^3 - 18d^2hks^2t - 2d^2hks^2x + 18d^2hkst^2 + 4d^2hkstx - 6d^2hkt^3 - 2d^2hkt^2x - 2d^2hs^2tw + 4d^2hst^2w - 2d^2ht^3w - 2d^2kls^3 + 6d^2kls^2t + d^2kls^2x - 6d^2klst^2 - 2d^2klstx + 2d^2klt^3 + d^2klt^2x - d^2kms^2x + 2d^2kmstx - d^2kmt^2x + 2d^2kns^2x - 4d^2knstx + 2d^2knt^2x - d^2kos^2x + 2d^2kostx - d^2kot^2x - 2d^2kqs^2y + 4d^2kqsty - 2d^2kqt^2y + d^2ls^2tw - 2d^2lst^2w + d^2lt^3w - d^2ms^2tw + 2d^2mst^2w - d^2mt^3w + 2d^2ns^2tw - 4d^2nst^2w + 2d^2nt^3w - d^2os^2tw + 2d^2ost^2w - d^2ot^3w - 2d^2qs^2tz + 4d^2qst^2z - 2d^2qt^3z - 2dfgks^3 + 6dfgks^2t - 6dfgkst^2 + 2dfgkt^3 + 2dfhks^3 - 6dfhks^2t + 6dfhkst^2 - 2dfhkt^3 + 6dgkqs^3 - 18dgkqs^2t + 18dgkqst^2 - 6dgkqt^3 - dgks^4 + 4dgks^3t - 6dgks^2t^2 + 4dgkst^3 - dgkt^4 - 8dhkqs^3 + 24dhkqs^2t - 24dhkqst^2 + 8dhkqt^3 + 2dhks^4 - 8dhks^3t + 12dhks^2t^2 - 8dhkst^3 + 2dhkt^4 + 2dklqs^3 - 6dklqs^2t + 6dklqst^2 - 2dklqt^3 - dkls^4 + 4dkls^3t - 6dkls^2t^2 + 4dklst^3 - dklt^4 - fgks^4 + 4fgks^3t - 6fgks^2t^2 + 4fgkst^3 - fgkt^4 + 2fhks^4 - 8fhks^3t + 12fhks^2t^2 - 8fhkst^3 + 2fhkt^4 - fkls^4 + 4fkls^3t - 6fkls^2t^2 + 4fklst^3 - fklt^4 + 2gkqs^4 - 8gkqs^3t + 12gkqs^2t^2 - 8gkqst^3 + 2gkqt^4 - 4hkqs^4 + 16hkqs^3t - 24hkqs^2t^2 + 16hkqst^3 - 4hkqt^4 + 2klqs^4 - 8klqs^3t + 12klqs^2t^2 - 8klqst^3 + 2klqt^4) / d^4k

				ad^4fz + ad^4km - ad^4ky + 2ad^3fsz + 4ad^3kms - 2ad^3kns - 2ad^3ksy + ad^2fs^2z + 6ad^2kms^2 - 6ad^2kns^2 + ad^2kos^2 - ad^2ks^2y + 4adkms^3 - 6adkns^3 + 2adkos^3 + akms^4 - 2akns^4 + akos^4- 2bd^3fsz - 2bd^3kms + 2bd^3ksy - 2bd^2fs^2z - 6bd^2kms^2 + 4bd^2kns^2 + 2bd^2ks^2y - 6bdkms^3 + 8bdkns^3 - 2bdkos^3 - 2bkms^4 + 4bkns^4 - 2bkos^4 + cd^2fs^2z + cd^2kms^2 - cd^2ks^2y

				- ad^4tz - 2ad^3ftz - 4ad^3kmt + 2ad^3knt + 2ad^3kty - 2ad^3stz - 2ad^2fstz - 12ad^2kmst + 12ad^2knst - 2ad^2kost + 2ad^2ksty - ad^2s^2tz - 12adkms^2t + 18adkns^2t - 6adkos^2t - 4akms^3t + 8akns^3t - 4akos^3t + 2bd^3ftz - 2bd^3kty + 2bd^3kmt + 2bd^3stz + 4bd^2fstz + 12bd^2kmst - 8bd^2knst - 4bd^2ksty + 2bd^2s^2tz + 18bdkms^2t - 24bdkns^2t + 6bdkos^2t + 8bkms^3t - 16bkns^3t + 8bkos^3t - 2cd^2fstz - 2cd^2kmst + 2cd^2ksty - cd^2s^2tz

				+ 2ad^3t^2z + ad^2ft^2z + 6ad^2kmt^2 - 6ad^2knt^2 + ad^2kot^2 - ad^2kt^2y + 2ad^2st^2z + 12adkmst^2 - 18adknst^2 + 6adkost^2 + 6akms^2t^2 - 12akns^2t^2 + 6akos^2t^2 - 2bd^3t^2z - 2bd^2ft^2z - 6bd^2kmt^2 + 4bd^2knt^2 + 2bd^2kt^2y - 4bd^2st^2z - 18bdkmst^2 + 24bdknst^2 - 6bdkost^2 - 12bkms^2t^2 + 24bkns^2t^2 - 12bkos^2t^2 + cd^2ft^2z + cd^2kmt^2 - cd^2kt^2y

				- ad^2t^3z - 4adkmt^3 + 6adknt^3 - 2adkot^3 - 4akmst^3 + 8aknst^3 - 4akost^3 + 2bd^2t^3z + 6bdkmt^3 - 8bdknt^3 + 2bdkot^3 + 8bkmst^3 - 16bknst^3 + 8bkost^3

				+ akmt^4 - 2aknt^4 + akot^4 - 2bkmt^4 + 4bknt^4 - 2bkot^4

				 
				 + 2cd^2st^2z - cd^2t^3z + 2cdkms^3 - 6cdkms^2t + 6cdkmst^2 - 2cdkmt^3 - 2cdkns^3 + 6cdkns^2t - 6cdknst^2 + 2cdknt^3 + ckms^4 - 4ckms^3t + 6ckms^2t^2 - 4ckmst^3 + ckmt^4 - 2ckns^4 + 8ckns^3t - 12ckns^2t^2 + 8cknst^3 - 2cknt^4 + ckos^4 - 4ckos^3t + 6ckos^2t^2 - 4ckost^3 + ckot^4 - d^5fz - d^5gk + d^5ky + d^5tz - d^4fgw + d^4fmw - 2d^4fsz + 2d^4ftz - 4d^4gks +4d^4gkt + d^4gkx + d^4gtw + 2d^4hks - 2d^4hkt - d^4kmx + 2d^4ksy - 2d^4kty - d^4mtw + 2d^4stz - 2d^4t^2z - 2d^3fgsw + 2d^3fgtw + 2d^3fhsw - 2d^3fhtw + 2d^3fmsw - 2d^3fmtw - 2d^3fnsw + 2d^3fntw + 2d^3fqsz - 2d^3fqtz - d^3fs^2z + 2d^3fstz - d^3ft^2z + 2d^3gkqs - 2d^3gkqt - 6d^3gks^2 + 12d^3gkst + 2d^3gksx - 6d^3gkt^2 - 2d^3gktx + 2d^3gstw - 2d^3gt^2w + 6d^3hks^2 - 12d^3hkst - 2d^3hksx + 6d^3hkt^2 + 2d^3hktx - 2d^3hstw + 2d^3ht^2w - d^3kls^2 + 2d^3klst - d^3klt^2 - 2d^3kmsx + 2d^3kmtx + 2d^3knsx - 2d^3kntx - 2d^3kqsy + 2d^3kqty + d^3ks^2y - 2d^3ksty + d^3kt^2y - 2d^3mstw + 2d^3mt^2w +2d^3nstw - 2d^3nt^2w - 2d^3qstz + 2d^3qt^2z + d^3s^2tz - 2d^3st^2z + d^3t^3z - d^2f^2s^2z + 2d^2f^2stz - d^2f^2t^2z - d^2fgks^2 + 2d^2fgkst - d^2fgkt^2 - d^2fgs^2w + 2d^2fgstw - d^2fgt^2w + 2d^2fhs^2w - 4d^2fhstw + 2d^2fht^2w + d^2fks^2y - 2d^2fksty + d^2fkt^2y - d^2fls^2w + 2d^2flstw - d^2flt^2w + d^2fms^2w - 2d^2fmstw + d^2fmt^2w - 2d^2fns^2w + 4d^2fnstw - 2d^2fnt^2w + d^2fos^2w - 2d^2fostw + d^2fot^2w + 2d^2fqs^2z - 4d^2fqstz + 2d^2fqt^2z + d^2fs^2tz - 2d^2fst^2z + d^2ft^3z + 6d^2gkqs^2 - 12d^2gkqst + 6d^2gkqt^2 - 4d^2gks^3 + 12d^2gks^2t + d^2gks^2x - 12d^2gkst^2 - 2d^2gkstx + 4d^2gkt^3 + d^2gkt^2x + d^2gs^2tw - 2d^2gst^2w + d^2gt^3w - 4d^2hkqs^2 + 8d^2hkqst - 4d^2hkqt^2 + 6d^2hks^3 - 18d^2hks^2t - 2d^2hks^2x + 18d^2hkst^2 + 4d^2hkstx - 6d^2hkt^3 - 2d^2hkt^2x - 2d^2hs^2tw + 4d^2hst^2w - 2d^2ht^3w - 2d^2kls^3 + 6d^2kls^2t + d^2kls^2x - 6d^2klst^2 - 2d^2klstx + 2d^2klt^3 + d^2klt^2x - d^2kms^2x + 2d^2kmstx - d^2kmt^2x + 2d^2kns^2x - 4d^2knstx + 2d^2knt^2x - d^2kos^2x + 2d^2kostx - d^2kot^2x - 2d^2kqs^2y + 4d^2kqsty - 2d^2kqt^2y + d^2ls^2tw - 2d^2lst^2w + d^2lt^3w - d^2ms^2tw + 2d^2mst^2w - d^2mt^3w + 2d^2ns^2tw - 4d^2nst^2w + 2d^2nt^3w - d^2os^2tw + 2d^2ost^2w - d^2ot^3w - 2d^2qs^2tz + 4d^2qst^2z - 2d^2qt^3z - 2dfgks^3 + 6dfgks^2t - 6dfgkst^2 + 2dfgkt^3 + 2dfhks^3 - 6dfhks^2t + 6dfhkst^2 - 2dfhkt^3 + 6dgkqs^3 - 18dgkqs^2t + 18dgkqst^2 - 6dgkqt^3 - dgks^4 + 4dgks^3t - 6dgks^2t^2 + 4dgkst^3 - dgkt^4 - 8dhkqs^3 + 24dhkqs^2t - 24dhkqst^2 + 8dhkqt^3 + 2dhks^4 - 8dhks^3t + 12dhks^2t^2 - 8dhkst^3 + 2dhkt^4 + 2dklqs^3 - 6dklqs^2t + 6dklqst^2 - 2dklqt^3 - dkls^4 + 4dkls^3t - 6dkls^2t^2 + 4dklst^3 - dklt^4 - fgks^4 + 4fgks^3t - 6fgks^2t^2 + 4fgkst^3 - fgkt^4 + 2fhks^4 - 8fhks^3t + 12fhks^2t^2 - 8fhkst^3 + 2fhkt^4 - fkls^4 + 4fkls^3t - 6fkls^2t^2 + 4fklst^3 - fklt^4 + 2gkqs^4 - 8gkqs^3t + 12gkqs^2t^2 - 8gkqst^3 + 2gkqt^4 - 4hkqs^4 + 16hkqs^3t - 24hkqs^2t^2 + 16hkqst^3 - 4hkqt^4 + 2klqs^4 - 8klqs^3t + 12klqs^2t^2 - 8klqst^3 + 2klqt^4) / d^4k


                """

                done = False

                if col == 0:
                    #exec_time, r = get_solutions_2(a, b, c, g, h, l, r, q, f, m, _n, o, d, ix, x, y, w, z, v, k, it0)

                    f = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By)
                    exec_time, r = get_solutions(f, t, it0)

                    """
                    print('')
                    print(r)
                    print('')
                    print(r_1)
                    print('')
                    """

                    """
					NI: 1: [t0: 1715.61, x: 18.86, y: 6.45, t1: 1758.17, x: 19.03, y: 7.13]
					Exec. Time: 0.39sec, NI: 3
					
					NI: 1: [t0: 1715.61, x: 18.86, y: 6.45, t1: 1758.17, x: 19.03, y: 7.13]
					Exec. Time: 0.00sec, NI: 3
                    """

                    solver_exec_time += exec_time
                    solver_exec_times += 1
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
                        if col == 1:
                            f = Cy - By
                        else:
                            f = Cx - Bx

                        exec_time, r = get_solutions(f, t, it0)

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
                        if col == 1:
                            f = Cy - Ay
                        else:
                            f = Cx - Ax

                        exec_time, r0 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        if col == 1:
                            f = Cy - By
                        else:
                            f = Cx - Bx

                        exec_time, r1 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        r = r0 + r1

                if not done:
                    r.sort()

                    inc = 0
                    a = None
                    b = None

                    for root in r:
                        Px, Py = mp.at(root)
                        Ax, Ay, Bx, By = msu.at(root)

                        # Is the point on the segment?
                        if (min(Ax, Bx) - epsilon <= Px and Px <= max(Ax, Bx) + epsilon) and (min(Ay, By) - epsilon <= Py and Py <= max(Ay, By) + epsilon):
                            inc += 1
                            n = len(s)

                            if col != 0:
                                if inc == 1:
                                    a = root
                                else:
                                    b = root
                            else:
                                if n == 0:
                                    s += [root]
                                else:
                                    prev = s[n-1]

                                    if isinstance(prev, Interval):
                                        if not prev.contains(root):
                                            s += [root]
                                    else:
                                        if root != prev:
                                            s += [root]

                    if col != 0:
                        n = len(s)

                        if a != None and b != None:
                            if n == 0:
                                s += [Interval(a, b, True, True)]
                            else:
                                prev = s[n-1]

                                if isinstance(prev, Interval):
                                    if not prev.contains(a):
                                        s += [Interval(a, b, True, True)]
                                    else:
                                        prev.y = b
                                else:
                                    if a != prev:
                                        s += [Interval(a, b, True, True)]
                                    else:
	                                    s[n-1] = Interval(a, b, True, True)
                        elif a != None and b == None:
                            if n == 0:
                                if a == it0.y:
                                    s += [a]
                                else:
                                    s += [Interval(a, it0.y, True, True)]
                            else:
                                prev = s[n-1]

                                if isinstance(prev, Interval):
                                    if not prev.contains(a):
                                        if a == it0.y:
                                            s += [a]
                                        else:
                                            s += [Interval(a, it0.y, True, True)]
                                    else:
                                        if a < it0.y and prev.y < it0.y:
                                            prev.y = it0.y
                                else:
                                    if a != prev:
                                        if a == it0.y:
                                            s += [a]
                                        else:
                                            s += [Interval(a, it0.y, True, True)]
                                    else:
                                        if a < it0.y:
	                                        s[n-1] = Interval(a, it0.y, True, True)

                idx += 1

        # Next unit(s).
        if msu.i.y == mpu.i.y:
            idxms += 1
            idxmp += 1
        elif msu.i.y < mpu.i.y:
            idxms += 1
        else:
            idxmp += 1


    # sort
    if prev != None:
        i = 0
        j = 0

        _sorted = []

        n = len(prev)
        m = len(s)

        while i < n and j < m:
            x1 = prev[i]
            x2 = s[j]

            if isinstance(x1, Interval) and isinstance(x2, Interval):
                ix0 = x1.begin()
                ix1 = x1.end()
                ix2 = x2.begin()
                ix3 = x2.end()

                if ix1 <= ix2:
                    _sorted += [x1]
                    i += 1
                elif ix3 <= ix0:
                    _sorted += [x2]
                    j += 1
                else:
                    print('ERR: Interval overlap. ' + x1.to_string() + ' ' + x2.to_string())
            elif isinstance(x1, Interval):
                ix0 = x1.begin()
                ix1 = x1.end()

                if x2 < ix0:
                    _sorted += [x2]
                    j += 1
                elif x2 > ix1:
                    _sorted += [x1]
                    i += 1
                else:
                    _sorted += [x1]
                    i += 1
                    j += 1
            elif isinstance(x2, Interval):
                ix0 = x2.begin()
                ix1 = x2.end()

                if x1 < ix0:
                    _sorted += [x1]
                    i += 1
                elif x1 > ix1:
                    _sorted += [x2]
                    j += 1
                else:
                    _sorted += [x2]
                    i += 1
                    j += 1
            else:
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
            _sorted += [prev[i]]
            i += 1

        while j < m:
            _sorted += [s[j]]
            j += 1

        s = _sorted

    return s

def get_intersections_2(ms, mp, i, prev = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon

    s = []
    t = Symbol('t')
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

                col = collinear(msu.c0.curves[idx].cp0, msu.c0.curves[idx].cp1, msu.c0.curves[idx].cp2, msu.c1.curves[idx].cp0, msu.c1.curves[idx].cp1, msu.c1.curves[idx].cp2, mpu.p[0], mpu.p[1])

                dt = msu.c0.intervals[idx].y - msu.c0.intervals[idx].x
                T = (t - msu.c0.intervals[idx].x) / dt

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

                Ax, Ay = msu.c0.curves[idx].at(T)
                Bx, By = msu.c1.curves[idx].at(T)

                dt = mpu.i.y - mpu.i.x
                T = (t - mpu.i.x) / dt
                Cx, Cy = mpu.at(T)

                mpu_t0 = mpu.i.x
                mpu_dt = dt

                x0 = mpu.p[0].x
                y0 = mpu.p[0].y

                dx = mpu.p[1].x - mpu.p[0].x
                dy = mpu.p[1].y - mpu.p[0].y

                """
                Ax = A*((T-s)/d)^2 - 2*A*((T-s)/d) + A + 2*B*((T-s)/d) - 2*B*((T-s)/d)^2 + C*((T-s)/d)^2
				Bx = R*((T-s)/d)^2 - 2*R*((T-s)/d) + R + 2*Q*((T-s)/d) - 2*Q*((T-s)/d)^2 + F*((T-s)/d)^2
                Ay = G*((T-s)/d)^2 - 2*G*((T-s)/d) + G + 2*H*((T-s)/d) - 2*H*((T-s)/d)^2 + L*((T-s)/d)^2
				By = M*((T-s)/d)^2 - 2*M*((T-s)/d) + M + 2*N*((T-s)/d) - 2*N*((T-s)/d)^2 + O*((T-s)/d)^2
                Cx = x + w*((T-v)/k)
                Cy = y + z*((T-v)/k)

                f = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By)

                (A*((T-s)/d)^2 - 2*A*((T-s)/d) + A + 2*B*((T-s)/d) - 2*B*((T-s)/d)^2 + C*((T-s)/d)^2) * ((M*((T-s)/d)^2 - 2*M*((T-s)/d) + M + 2*N*((T-s)/d) - 2*N*((T-s)/d)^2 + O*((T-s)/d)^2) - (y + z*((T-v)/k))) + (R*((T-s)/d)^2 - 2*R*((T-s)/d) + R + 2*Q*((T-s)/d) - 2*Q*((T-s)/d)^2 + F*((T-s)/d)^2) * ((y + z*((T-v)/k)) - (G*((T-s)/d)^2 - 2*G*((T-s)/d) + G + 2*H*((T-s)/d) - 2*H*((T-s)/d)^2 + L*((T-s)/d)^2)) + (x + w*((T-v)/k)) * ((G*((T-s)/d)^2 - 2*G*((T-s)/d) + G + 2*H*((T-s)/d) - 2*H*((T-s)/d)^2 + L*((T-s)/d)^2) - (M*((T-s)/d)^2 - 2*M*((T-s)/d) + M + 2*N*((T-s)/d) - 2*N*((T-s)/d)^2 + O*((T-s)/d)^2))

                # https://www.mathpapa.com/simplify-calculator/

                Cy - By
				(y + z*((T-v)/k)) - (M*((T-s)/d)^2 - 2*M*((T-s)/d) + M + 2*N*((T-s)/d) - 2*N*((T-s)/d)^2 + O*((T-s)/d)^2)
				-d2km+d2ky+d2tz-d2vz-2dkms+2dkmt+2dkns-2dknt-kms2+2kmst-kmt2+2kns2-4knst+2knt2-kos2+2kost-kot2
				d**2*k

                Cx - Bx
				(x + w*((T-v)/k)) - (R*((T-s)/d)^2 - 2*R*((T-s)/d) + R + 2*Q*((T-s)/d) - 2*Q*((T-s)/d)^2 + F*((T-s)/d)^2)
                -d2kr+d2kx+d2tw-d2vw+2dkqs-2dkqt-2dkrs+2dkrt-fks2+2fkst-fkt2+2kqs2-4kqst+2kqt2-krs2+2krst-krt2
				d**2*k
				
				Cy - Ay
				(y + z*((T-v)/k)) - (G*((T-s)/d)^2 - 2*G*((T-s)/d) + G + 2*H*((T-s)/d) - 2*H*((T-s)/d)^2 + L*((T-s)/d)^2)
                -d2gk+d2ky+d2tz-d2vz-2dgks+2dgkt+2dhks-2dhkt-gks2+2gkst-gkt2+2hks2-4hkst+2hkt2-kls2+2klst-klt2
				d**2*k

				Cx - Ax
				(x + w*((T-v)/k)) - (A*((T-s)/d)^2 - 2*A*((T-s)/d) + A + 2*B*((T-s)/d) - 2*B*((T-s)/d)^2 + C*((T-s)/d)^2)
				-ad2k-2adks+2adkt-aks2+2akst-akt2+2bdks-2bdkt+2bks2-4bkst+2bkt2-cks2+2ckst-ckt2+d2kx+d2tw-d2vw
				d**2*k
				"""

                done = False

                # Generic case where not all elements travel in the same trajectory.
                if col == 0:
                    exec_time, r = get_solutions_quartic(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu_dt, msu_t0, x0, y0, dx, dy, mpu_t0, mpu_dt, it0)

                    #f = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By)
                    #exec_time, r = get_solutions(f, t, it0)

                    solver_exec_time += exec_time
                    solver_exec_times += 1
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

                if not done:
                    r.sort()

                    inc = 0
                    a = None
                    b = None

                    for root in r:
                        Px, Py = mp.at(root)
                        Ax, Ay, Bx, By = msu.at(root)

                        # Is the point on the segment?
                        if (min(Ax, Bx) - epsilon <= Px and Px <= max(Ax, Bx) + epsilon) and (min(Ay, By) - epsilon <= Py and Py <= max(Ay, By) + epsilon):
                            inc += 1
                            n = len(s)

                            if col != 0:
                                if inc == 1:
                                    a = root
                                else:
                                    b = root
                            else:
                                if n == 0:
                                    s += [root]
                                else:
                                    prev = s[n-1]

                                    if isinstance(prev, Interval):
                                        if not prev.contains(root):
                                            s += [root]
                                    else:
                                        if root != prev:
                                            s += [root]

                    if col != 0:
                        n = len(s)

                        if a != None and b != None:
                            if n == 0:
                                s += [Interval(a, b, True, True)]
                            else:
                                prev = s[n-1]

                                if isinstance(prev, Interval):
                                    if not prev.contains(a):
                                        s += [Interval(a, b, True, True)]
                                    else:
                                        prev.y = b
                                else:
                                    if a != prev:
                                        s += [Interval(a, b, True, True)]
                                    else:
	                                    s[n-1] = Interval(a, b, True, True)
                        elif a != None and b == None:
                            if n == 0:
                                if a == it0.y:
                                    s += [a]
                                else:
                                    s += [Interval(a, it0.y, True, True)]
                            else:
                                prev = s[n-1]

                                if isinstance(prev, Interval):
                                    if not prev.contains(a):
                                        if a == it0.y:
                                            s += [a]
                                        else:
                                            s += [Interval(a, it0.y, True, True)]
                                    else:
                                        if a < it0.y and prev.y < it0.y:
                                            prev.y = it0.y
                                else:
                                    if a != prev:
                                        if a == it0.y:
                                            s += [a]
                                        else:
                                            s += [Interval(a, it0.y, True, True)]
                                    else:
                                        if a < it0.y:
	                                        s[n-1] = Interval(a, it0.y, True, True)

                idx += 1

        # Next unit(s).
        if msu.i.y == mpu.i.y:
            idxms += 1
            idxmp += 1
        elif msu.i.y < mpu.i.y:
            idxms += 1
        else:
            idxmp += 1

    # sort intersections
    if prev != None:
        i = 0
        j = 0

        _sorted = []

        n = len(prev)
        m = len(s)

        while i < n and j < m:
            x1 = prev[i]
            x2 = s[j]

            if isinstance(x1, Interval) and isinstance(x2, Interval):
                ix0 = x1.begin()
                ix1 = x1.end()
                ix2 = x2.begin()
                ix3 = x2.end()

                if ix1 <= ix2:
                    _sorted += [x1]
                    i += 1
                elif ix3 <= ix0:
                    _sorted += [x2]
                    j += 1
                else:
                    print('ERR: Interval overlap. ' + x1.to_string() + ' ' + x2.to_string())
            elif isinstance(x1, Interval):
                ix0 = x1.begin()
                ix1 = x1.end()

                if x2 < ix0:
                    _sorted += [x2]
                    j += 1
                elif x2 > ix1:
                    _sorted += [x1]
                    i += 1
                else:
                    _sorted += [x1]
                    i += 1
                    j += 1
            elif isinstance(x2, Interval):
                ix0 = x2.begin()
                ix1 = x2.end()

                if x1 < ix0:
                    _sorted += [x1]
                    i += 1
                elif x1 > ix1:
                    _sorted += [x2]
                    j += 1
                else:
                    _sorted += [x2]
                    i += 1
                    j += 1
            else:
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
            _sorted += [prev[i]]
            i += 1

        while j < m:
            _sorted += [s[j]]
            j += 1

        s = _sorted

    return s

def get_intersections_3(ms, mp, i, prev_it = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon

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

                done = False
                col = 0

                # Generic case where not all elements travel in the same trajectory.
                if col == 0:
                    exec_time, r = get_solutions_quartic(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu_dt, msu_t0, x0, y0, dx, dy, mpu_t0, mpu_dt, it0)

                    #f = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By)
                    #exec_time, r = get_solutions(f, t, it0)

                    solver_exec_time += exec_time
                    solver_exec_times += 1
                # special cases
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


                # check if roots are on the segment (are valid)
                # roots not in the interval have already been discarded in get_solutions_quartic

                if not done:
                    roots = []

                    for root in r:
                        Px, Py = mp.at(root)
                        Ax, Ay, Bx, By = msu.at(root)

                        if on_segment_with_eps(Ax, Ay, Bx, By, Px, Py, epsilon):
                            roots += [root]

                    s = roots
                    s.sort()

                """
                if not done:
                    r.sort()

                    inc = 0
                    a = None
                    b = None

                    for root in r:
                        Px, Py = mp.at(root)
                        Ax, Ay, Bx, By = msu.at(root)

                        # Is the point on the segment?
                        if (min(Ax, Bx) - epsilon <= Px and Px <= max(Ax, Bx) + epsilon) and (min(Ay, By) - epsilon <= Py and Py <= max(Ay, By) + epsilon):
                            inc += 1
                            n = len(s)

                            if col != 0:
                                if inc == 1:
                                    a = root
                                else:
                                    b = root
                            else:
                                if n == 0:
                                    s += [root]
                                else:
                                    prev = s[n-1]

                                    if isinstance(prev, Interval):
                                        if not prev.contains(root):
                                            s += [root]
                                    else:
                                        if root != prev:
                                            s += [root]

                    if col != 0:
                        n = len(s)

                        if a != None and b != None:
                            if n == 0:
                                s += [Interval(a, b, True, True)]
                            else:
                                prev = s[n-1]

                                if isinstance(prev, Interval):
                                    if not prev.contains(a):
                                        s += [Interval(a, b, True, True)]
                                    else:
                                        prev.y = b
                                else:
                                    if a != prev:
                                        s += [Interval(a, b, True, True)]
                                    else:
	                                    s[n-1] = Interval(a, b, True, True)
                        elif a != None and b == None:
                            if n == 0:
                                if a == it0.y:
                                    s += [a]
                                else:
                                    s += [Interval(a, it0.y, True, True)]
                            else:
                                prev = s[n-1]

                                if isinstance(prev, Interval):
                                    if not prev.contains(a):
                                        if a == it0.y:
                                            s += [a]
                                        else:
                                            s += [Interval(a, it0.y, True, True)]
                                    else:
                                        if a < it0.y and prev.y < it0.y:
                                            prev.y = it0.y
                                else:
                                    if a != prev:
                                        if a == it0.y:
                                            s += [a]
                                        else:
                                            s += [Interval(a, it0.y, True, True)]
                                    else:
                                        if a < it0.y:
	                                        s[n-1] = Interval(a, it0.y, True, True)
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

            """
            if isinstance(x1, Interval) and isinstance(x2, Interval):
                ix0 = x1.begin()
                ix1 = x1.end()
                ix2 = x2.begin()
                ix3 = x2.end()

                if ix1 <= ix2:
                    _sorted += [x1]
                    i += 1
                elif ix3 <= ix0:
                    _sorted += [x2]
                    j += 1
                else:
                    print('ERR: Interval overlap. ' + x1.to_string() + ' ' + x2.to_string())
            elif isinstance(x1, Interval):
                ix0 = x1.begin()
                ix1 = x1.end()

                if x2 < ix0:
                    _sorted += [x2]
                    j += 1
                elif x2 > ix1:
                    _sorted += [x1]
                    i += 1
                else:
                    _sorted += [x1]
                    i += 1
                    j += 1
            elif isinstance(x2, Interval):
                ix0 = x2.begin()
                ix1 = x2.end()

                if x1 < ix0:
                    _sorted += [x1]
                    i += 1
                elif x1 > ix1:
                    _sorted += [x2]
                    j += 1
                else:
                    _sorted += [x2]
                    i += 1
                    j += 1
            else:
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
            """

        while i < n:
            _sorted += [prev_it[i]]
            i += 1

        while j < m:
            _sorted += [s[j]]
            j += 1

        s = _sorted

    return s

def get_intersections_4(ms, mp, i, prev_it = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon

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

                """
                dt = mpu.i.y - mpu.i.x

                mpu_t0 = mpu.i.x
                mpu_dt = dt

                x0 = mpu.p[0].x
                y0 = mpu.p[0].y

                dx = mpu.p[1].x - mpu.p[0].x
                dy = mpu.p[1].y - mpu.p[0].y
                """

                done = False
                col = 0

                # Generic case where not all elements travel in the same trajectory.
                if col == 0:
                    exec_time, r = get_solutions_quartic2(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu_dt, msu_t0, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, mpu_t0, mpu_dt, it0)

                    #f = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By)
                    #exec_time, r = get_solutions(f, t, it0)

                    solver_exec_time += exec_time
                    solver_exec_times += 1
                # special cases
                else:
                    pass

                #print('>>>>>>>>>')

                if not done:
                    roots = []

                    for root in r:
                        #print('>', root)
                        Px, Py = mp.at(root)
                        #print('<')
                        Ax, Ay, Bx, By = msu.at(root)

                        if on_segment_with_eps(Ax, Ay, Bx, By, Px, Py, epsilon):
                            roots += [root]

                    s = roots
                    s.sort()

                idx += 1

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

#-------------------------------------------------------------------
# Touch times between a moving seg and a moving point
#-------------------------------------------------------------------
def get_touch_times(ms, mp, i):
    global solver_exec_time
    global solver_exec_times
    global epsilon

    s = []
    t = Symbol('t')
    idxms = 0
    idxmp = 0
    end = 0

    while idxms < len(ms.units) and idxmp < len(mp.units):
        msu = ms.units[idxms]
        mpu = mp.units[idxmp]

        # Leave early.
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

        # Intersection between the two units.
        it = it0.intersection(it1)

        if it != None:
            idx = 0
            n = len(msu.c0.intervals)

            while idx < n:
                it0 = msu.c0.intervals[idx].intersection(it)
                if it0 is None:
                    idx += 1
                    continue

                col = collinear(msu.c0.curves[idx].cp0, msu.c0.curves[idx].cp1, msu.c0.curves[idx].cp2, msu.c1.curves[idx].cp0, msu.c1.curves[idx].cp1, msu.c1.curves[idx].cp2, mpu.p[0], mpu.p[1])

                # MSeg
                dt = msu.c0.intervals[idx].y - msu.c0.intervals[idx].x
                T = (t - msu.c0.intervals[idx].x) / dt
                Ax, Ay = msu.c0.curves[idx].at(T)
                Bx, By = msu.c1.curves[idx].at(T)

                # MPoint
                dt = mpu.i.y - mpu.i.x
                T = (t - mpu.i.x) / dt
                Cx, Cy = mpu.at(T)

                if col == 0 or coll == 3:
                    f = Ax - Cx - Ay + Cy
                    exec_time, r0 = get_solutions(f, t, it0)

                    solver_exec_time += exec_time
                    solver_exec_times += 1

                    f = Bx - Cx - By + Cy
                    exec_time, r1 = get_solutions(f, t, it0)

                    solver_exec_time += exec_time
                    solver_exec_times += 1

                    r = r0 + r1
                else:
                    # VL.
                    if col == 1:
                        f = Ay - Cy
                        exec_time, r0 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        f = By - Cy
                        exec_time, r1 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        r = r0 + r1
                    # HL.
                    elif col == 2:
                        f = Ax - Cx
                        exec_time, r0 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        f = Bx - Cx
                        exec_time, r1 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        r = r0 + r1
                    # GL.
                    """
                    else:
                    """

                    """
                    Px0, Py0 = mp.at(it0.x)
                    Ax0, Ay0, Bx0, By0 = msu.at(it0.x)

                    Px1, Py1 = mp.at(it0.y)
                    Ax1, Ay1, Bx1, By1 = msu.at(it0.y)

                    sin = (min(Ax0, Bx0) - epsilon <= Px0 and Px0 <= max(Ax0, Bx0) + epsilon) and (min(Ay0, By0) - epsilon <= Py0 and Py0 <= max(Ay0, By0) + epsilon)
                    sou = (min(Ax1, Bx1) - epsilon <= Px1 and Px1 <= max(Ax1, Bx1) + epsilon) and (min(Ay1, By1) - epsilon <= Py1 and Py1 <= max(Ay1, By1) + epsilon)

                    n = len(s)

                    # The MP is inside the MS.
                    if sin and sou:
                        done = True
                    elif sin:
                        if col == 1:
                            f = Cy - By
                        else:
                            f = Cx - Bx

                        exec_time, r = get_solutions(f, t, it0)

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
                        if col == 1:
                            f = Cy - Ay
                        else:
                            f = Cx - Ax

                        exec_time, r0 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        if col == 1:
                            f = Cy - By
                        else:
                            f = Cx - Bx

                        exec_time, r1 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        r = r0 + r1
                    """

                r.sort()

                for root in r:
                    Px, Py = mp.at(root)
                    Ax, Ay, Bx, By = msu.at(root)

                    # Validation.
                    if (Ax - epsilon <= Px and Px <= Ax + epsilon and Ay - epsilon <= Py and Py <= Ay + epsilon) or (Bx - epsilon <= Px and Px <= Bx + epsilon and By - epsilon <= Py and Py <= By + epsilon):
                        n = len(s)
                        if n == 0:
                            s += [root]
                        else:
                            prev = s[n-1]

                            if isinstance(prev, Interval):
                                if not prev.contains(root):
                                    s += [root]
                            else:
                                if root != prev:
                                    s += [root]

                idx += 1

        # Next unit(s).
        if msu.i.y == mpu.i.y:
            idxms += 1
            idxmp += 1
        elif msu.i.y < mpu.i.y:
            idxms += 1
        else:
            idxmp += 1

    return s

#-------------------------------------------------------------------
# Equals times between a moving seg and a moving point
#-------------------------------------------------------------------
def get_equals_times(ms, mp, i):
    global solver_exec_time
    global solver_exec_times
    global epsilon

    s = []
    t = Symbol('t')
    idxms = 0
    idxmp = 0
    end = 0

    while idxms < len(ms.units) and idxmp < len(mp.units):
        msu = ms.units[idxms]
        mpu = mp.units[idxmp]

        # Leave early.
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

        # Intersection between the two units.
        it = it0.intersection(it1)

        if it != None:
            idx = 0
            n = len(msu.c0.intervals)

            while idx < n:
                it0 = msu.c0.intervals[idx].intersection(it)
                if it0 is None:
                    idx += 1
                    continue

                col = collinear(msu.c0.curves[idx].cp0, msu.c0.curves[idx].cp1, msu.c0.curves[idx].cp2, msu.c1.curves[idx].cp0, msu.c1.curves[idx].cp1, msu.c1.curves[idx].cp2, mpu.p[0], mpu.p[1])

                # MSeg
                dt = msu.c0.intervals[idx].y - msu.c0.intervals[idx].x
                T = (t - msu.c0.intervals[idx].x) / dt
                Ax, Ay = msu.c0.curves[idx].at(T)
                Bx, By = msu.c1.curves[idx].at(T)

                # MPoint
                dt = mpu.i.y - mpu.i.x
                T = (t - mpu.i.x) / dt
                Cx, Cy = mpu.at(T)

                if col == 0 or coll == 3:
                    f = Ax - Cx - Ay + Cy
                    exec_time, r0 = get_solutions(f, t, it0)

                    solver_exec_time += exec_time
                    solver_exec_times += 1

                    f = Bx - Cx - By + Cy
                    exec_time, r1 = get_solutions(f, t, it0)

                    solver_exec_time += exec_time
                    solver_exec_times += 1
                else:
                    # VL.
                    if col == 1:
                        f = Ay - Cy
                        exec_time, r0 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        f = By - Cy
                        exec_time, r1 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1
                    # HL.
                    elif col == 2:
                        f = Ax - Cx
                        exec_time, r0 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        f = Bx - Cx
                        exec_time, r1 = get_solutions(f, t, it0)

                        solver_exec_time += exec_time
                        solver_exec_times += 1

                r = []
                r0.sort()
                r1.sort()

                idr0 = 0
                idr1 = 0

                n0 = len(r0)
                n1 = len(r1)

                while idr0 < n0 and idr1 < n1:
                    if r0[idr0] == r1[idr1]:
                        r += [r0[idr0]]
                        idr0 += 1
                        idr1 += 1
                    elif r0[idr0] < r1[idr1]:
                        idr0 += 1
                    else:
                        idr1 += 1

                for root in r:
                    Px, Py = mp.at(root)
                    Ax, Ay, Bx, By = msu.at(root)

                    # Validation.
                    if (Ax - epsilon <= Px and Px <= Ax + epsilon and Ay - epsilon <= Py and Py <= Ay + epsilon) or (Bx - epsilon <= Px and Px <= Bx + epsilon and By - epsilon <= Py and Py <= By + epsilon):
                        n = len(s)
                        if n == 0:
                            s += [root]
                        else:
                            prev = s[n-1]

                            if isinstance(prev, Interval):
                                if not prev.contains(root):
                                    s += [root]
                            else:
                                if root != prev:
                                    s += [root]

                idx += 1

        # Next unit(s).
        if msu.i.y == mpu.i.y:
            idxms += 1
            idxmp += 1
        elif msu.i.y < mpu.i.y:
            idxms += 1
        else:
            idxmp += 1

    return s

#-------------------------------------------------------------------
# Get complementary interval
#-------------------------------------------------------------------
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

"""
	Test moving region - moving point intersection.
"""
def test_mr_mp_int():
    #1,2,7,5.5,12,8
    #7,5,16.5,6.5,25,7
    #9,1,11.5,2.5,13,4

    s1 = '1,2,7,5.5,12,8#7,5,16.5,6.9,25,7#1000,2000:1000,2000'
    #s1 = '1,1,2,0,3.25,0.9#4,4,5,3,6.2,3.4#1000,2000:1000,2000'
    s2 = '1,2,7,5.5,12,8#9,1,11.5,2.5,13,4#1000,2000:1000,2000'
    s3 = '7,5,16.5,6.9,25,7#9,1,11.5,2.5,13,4#1000,2000:1000,2000'

    #p1 = '1.25,-0.7#7.25,4.25#1000,2000'
    # no intersection
    #p1 = '16,-5#27,11#1000,2000'
    p1 = '16,-5#20,11#1000,2000'

    ms1 = create_moving_segment([s1], pass_through_control_points)
    ms2 = create_moving_segment([s2], pass_through_control_points)
    ms3 = create_moving_segment([s3], pass_through_control_points)

    mp1 = create_moving_point([p1])

    """
    intersections1 = []
    intersections2 = []
    intersections3 = []

    
    intersections1 = get_intersection_times(ms1, mp1, interval)
    intersections2 = get_intersection_times(ms2, mp1, interval)
    intersections3 = get_intersection_times(ms3, mp1, interval)
    
    intersections = []

    i = 0
    j = 0
    k = 0

    n = len(intersections1)
    m = len(intersections2)
    o = len(intersections3)

    while i < n and j < m and k < o:
        x1 = intersections1[i]
        x2 = intersections2[j]
        x3 = intersections3[k]

        if x1 < x2:
            if x1 < x3:
                intersections += [x1]
        elif x1 == x2:
            
        else:
    """        

    """
    intersections1 = get_intersection_times(ms1, mp1, interval)
    intersections1 += get_intersection_times(ms2, mp1, interval)
    intersections1 += get_intersection_times(ms3, mp1, interval)
    """

    intersections = get_intersections(ms1, mp1, interval)
    intersections = get_intersections(ms2, mp1, interval, intersections)
    intersections = get_intersections(ms3, mp1, interval, intersections)

    """
	NI: 1: [t0: 1715.61, x: 18.86, y: 6.45, t1: 1758.17, x: 19.03, y: 7.13]
	Exec. Time: 0.00sec, NI: 3

	NI: 1: [t0: 1715.61, x: 18.86, y: 6.45, t1: 1758.17, x: 19.03, y: 7.13]
	Exec. Time: 0.00sec, NI: 3
	"""

    """
    intersections = get_intersections_2(ms1, mp1, interval)
    intersections = get_intersections_2(ms2, mp1, interval, intersections)
    intersections = get_intersections_2(ms3, mp1, interval, intersections)
    """

    # rearange
    n = len(intersections)
    if n > 1:
        i = 0
        _intersections = []
        while i < n:
            i0 = intersections[i]
            i1 = intersections[i+1]

            """
            if isinstance(i0, Interval) and isinstance(i1, Interval):
                t0 = i0.begin()
                t1 = i0.end()
                t2 = i1.begin()
                t3 = i1.end()
                if t1 == t2
            if isinstance(t, Interval):
            """

            if isinstance(i0, Interval):
                _intersections += [i0]
                i += 1
            elif not isinstance(i1, Interval):
                _intersections += [Interval(i0, i1, True, True)]
                i += 2
            else:
                print('ERR: instant followed by interval in the intersections list.')
                sys.exit()

        if isinstance(intersections[n-1], Interval):
            _intersections += [intersections[n-1]]

        intersections = _intersections
    # sort intersections1

    MS = [ms1, ms2, ms3]
	#I = [intersections1, intersections2, intersections3]

    #get_samples_for_viz_2(MS, mp1, interval, n_samples, intersections1)
    get_samples_for_viz_2(MS, mp1, interval, n_samples, intersections)

    #get_samples_for_viz(ms1, mp1, interval, n_samples, intersections1)
    #get_samples_for_viz(ms2, mp1, interval, n_samples, intersections1)
    #get_samples_for_viz(ms3, mp1, interval, n_samples, intersections1)

    if print_intersection_information:
        #print(get_intersection_information(intersections1, ms1, mp1))
        print(get_intersection_information(intersections, ms1, mp1))

    if print_solver_execution_time:
        print("Exec. Time: "+ format(solver_exec_time, precision) + "sec, NI: " + str(solver_exec_times))

    sys.exit()

def test_mr_mp(s1, s2, s3, p1):
    #s1 = '1,2,7,5.5,12,8#7,5,16.5,6.9,25,7#1000,2000:1000,2000'
    #s2 = '1,2,7,5.5,12,8#9,1,11.5,2.5,13,4#1000,2000:1000,2000'
    #s3 = '7,5,16.5,6.9,25,7#9,1,11.5,2.5,13,4#1000,2000:1000,2000'

    #p1 = '16,-5#20,11#1000,2000'

    ms1 = create_moving_segment([s1], pass_through_control_points)
    ms2 = create_moving_segment([s2], pass_through_control_points)
    ms3 = create_moving_segment([s3], pass_through_control_points)

    mp1 = create_moving_point([p1])

    intersections = get_intersections(ms1, mp1, interval)
    intersections = get_intersections(ms2, mp1, interval, intersections)
    intersections = get_intersections(ms3, mp1, interval, intersections)

    # re-arrange
    n = len(intersections)
    if n > 1:
        i = 0
        _intersections = []
        while i < n:
            i0 = intersections[i]
            i1 = intersections[i+1]

            if isinstance(i0, Interval):
                _intersections += [i0]
                i += 1
            elif not isinstance(i1, Interval):
                _intersections += [Interval(i0, i1, True, True)]
                i += 2
            else:
                print('ERR: instant followed by interval in the intersections list.')
                sys.exit()

        if isinstance(intersections[n-1], Interval):
            _intersections += [intersections[n-1]]

        intersections = _intersections

    MS = [ms1, ms2, ms3]

    get_samples_for_viz_2(MS, mp1, interval, n_samples, intersections)

    if print_intersection_information:
        print(get_intersection_information(intersections, ms1, mp1))

    if print_solver_execution_time:
        print("Exec. Time: "+ format(solver_exec_time, precision) + "sec, NI: " + str(solver_exec_times))

#def test_mr_mp_2(s1, s2, s3, p1):
def test_mr_mp_2(MS, p):
    msegs = []
    for ms in MS:
        msegs += [create_moving_segment([ms], pass_through_control_points)]

    #ms1 = create_moving_segment([s1], pass_through_control_points)
    #ms2 = create_moving_segment([s2], pass_through_control_points)
    #ms3 = create_moving_segment([s3], pass_through_control_points)

    mp = create_moving_point([p])

    intersections = None

    #intersections = get_intersections_2(ms1, mp1, interval)
    #intersections = get_intersections_2(ms2, mp1, interval, intersections)
    #intersections = get_intersections_2(ms3, mp1, interval, intersections)

    for ms in msegs:    
        intersections = get_intersections_2(ms, mp, interval, intersections)

    # re-arrange
    n = len(intersections)

    if n > 1:
        i = 0
        _intersections = []
        while i < n:
            i0 = intersections[i]
            i1 = intersections[i+1]

            if isinstance(i0, Interval):
                _intersections += [i0]
                i += 1
            elif not isinstance(i1, Interval):
                _intersections += [Interval(i0, i1, True, True)]
                i += 2
            else:
                print('ERR: instant followed by interval in the intersections list.')
                sys.exit()

        if isinstance(intersections[n-1], Interval):
            _intersections += [intersections[n-1]]

        intersections = _intersections

    #MS = [ms1, ms2, ms3]

    #get_samples_for_viz_2(MS, mp1, interval, n_samples, intersections)
    get_samples_for_viz_2(msegs, mp, interval, n_samples, intersections)

    if print_intersection_information:
        #print(get_intersection_information(intersections, ms1, mp))
        print(get_intersection_information(intersections, msegs[0], mp))

    if print_solver_execution_time:
        print("Exec. Time: "+ format(solver_exec_time, precision) + "sec, NI: " + str(solver_exec_times))

def process_intersections(intersections, mp, msegs, initial_state, final_state):
    n = len(intersections)

    # 1 Intersection.
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
                    print_error(-1, 'process_intersections() Only one intersection, but not the one expected (1 Case).')
        # Inside
        elif initial_state == State.Inside:
            if intersection > interval.x:
                I = Interval(interval.x, intersection, True, True)
                intersections = [I]
        # Touch
        elif initial_state == State.Touch:
            if intersection != interval.x:
                print_error(-1, 'process_intersections() Only one intersection, but not the one expected (2 Case).')
    elif n > 1:
        i = 0
        _intersections = []

        if initial_state == None:
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
                    #_intersections += [t0]
                    #i += 1

                    if i == n-2:
                        _intersections += [t0, t1]
                        i += 2
                    else:
                        _intersections += [t0]
                        i += 1

        elif initial_state == State.Inside:
            t0 = intersections[0]
            t1 = intersections[1]

            I = Interval(t0, t1, True, True)
            _intersections += [I]
            i += 2

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
                    print_error(-1, 'process_intersections() : Invalid Observation (2 condition).')
                        
                if not reg.is_simple:
                    print_error(-1, 'process_intersections() : Non-simple Observation (2 condition).')

                if shapely.geometry.Point(Px, Py).within(reg):
                    I = Interval(t0, t1, True, True)
                    _intersections += [I]
                    i += 2
                else:
                    #_intersections += [t0]
                    #i += 1

                    if i == n-2:
                        _intersections += [t0, t1]
                        i += 2
                    else:
                        _intersections += [t0]
                        i += 1

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

        intersections = _intersections

    """
    # find intervals of intersection

    # touched or entered the region
    if n == 1 and intersections[0] != interval.y:
        # entered the region

        if final_state == State.Inside:
            I = Interval(intersections[0], interval.y, True, True)
            intersections = [I]
    elif n > 1:
        i = 0
        _intersections = []

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
                print_error(-1, 'get_moving_segs_from_observations() : Invalid Observation.')
                        
            if not reg.is_simple:
                print_error(-1, 'get_moving_segs_from_observations() : Non-simple Observation.')

            if shapely.geometry.Point(Px, Py).within(reg):
                I = Interval(t0, t1, True, True)
                _intersections += [I]
                i += 2
            else:
                _intersections += [t0]
                i += 1

        if i == n - 1:
            t = intersections[n - 1]

            if t != interval.y:
                if final_state == State.Inside:
                    I = Interval(t, interval.y, True, True)
                    _intersections += [I]
                else:
                    _intersections += [t]

        intersections = _intersections
    """

    return intersections

def get_region_at(msegs, t):

    coords = []
    k = 0

    x0, y0, x1, y1 = msegs[k].at(t)

    coords += [[x0, y0]]
    coords += [[x1, y1]]

    k = 1
    n = len(msegs)

    while k < n:
        x0, y0, x1, y1 = msegs[k].at(t)

        coords += [[x1, y1]]               
        k += 1

    reg = Polygon(coords)

    if not reg.is_valid:
        print_error(-1, 'get_moving_segs_from_observations() : Invalid Observation.')
                        
    if not reg.is_simple:
        print_error(-1, 'get_moving_segs_from_observations() : Non-simple Observation.')

    return reg

def seconds_to_time(sec):
    day = sec / (24 * 3600)
    sec = sec % (24 * 3600)
    hour = sec / 3600

    sec %= 3600
    minutes = sec / 60

    sec %= 60
    seconds = sec

    return day, hour, minutes, seconds

def get_mr_mp_intersections(MS, mp, initial_state, final_state, op = 1, p_linear_traj = False):
    global begin_exec_time
    global precision_0

    msegs = []

    for ms in MS:
        msegs += [create_moving_segment([ms], pass_through_control_points)]

    intersections = None

    if p_linear_traj:
        for ms in msegs:    
            intersections = get_intersections_4(ms, mp, interval, intersections)
    else:
        for ms in msegs:    
            intersections = get_intersections_3(ms, mp, interval, intersections)

    if initial_state == State.Inside or initial_state == State.Touch:# or initial_state == State.Intersect:
        intersections = [interval.begin()] + intersections

    if final_state == State.Inside or final_state == State.Touch:# or final_state == State.Intersect:
        intersections += [interval.end()]

    intersections = process_intersections(intersections, mp, msegs, initial_state, final_state)

    """
    if initial_state == State.Inside:
        intersections = [interval.begin()] + intersections

    n = len(intersections)

    # find intervals of intersection

    # touched or entered the region
    if n == 1 and intersections[0] != interval.y:
        # entered the region

        if final_state == State.Inside:
            I = Interval(intersections[0], interval.y, True, True)
            intersections = [I]
    elif n > 1:
        i = 0
        _intersections = []

        while i < n - 1:
            t0 = intersections[i]
            t1 = intersections[i+1]

            #I = Interval(t0, t1, True, True)
            #_intersections += [I]
            #i += 2

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
            #reg = reg.simplify(0.000001)
            #print(t, reg.wkt)

            if not reg.is_valid:
                print_error(-1, 'get_moving_segs_from_observations() : Invalid Observation.')
                        
            if not reg.is_simple:
                print_error(-1, 'get_moving_segs_from_observations() : Non-simple Observation.')

            if shapely.geometry.Point(Px, Py).within(reg):
                I = Interval(t0, t1, True, True)
                _intersections += [I]
                i += 2
            else:
                _intersections += [t0]
                i += 1
            
        #print(i, n, i == n - 1)

        if i == n - 1:
            t = intersections[n - 1]

            if t != interval.y:
                if final_state == State.Inside:
                    I = Interval(t, interval.y, True, True)
                    _intersections += [I]
                else:
                    _intersections += [t]

        #if isinstance(intersections[n-1], Interval):
        #    _intersections += [intersections[n-1]]

        intersections = _intersections
    """

    """
    if n > 1:
        i = 0
        _intersections = []

        while i < n:
            i0 = intersections[i]
            i1 = intersections[i+1]

            if isinstance(i0, Interval):
                _intersections += [i0]
                i += 1
            elif not isinstance(i1, Interval):
                _intersections += [Interval(i0, i1, True, True)]
                i += 2
            else:
                print('ERR: instant followed by interval in the intersections list.')
                sys.exit()

        if isinstance(intersections[n-1], Interval):
            _intersections += [intersections[n-1]]

        intersections = _intersections
    """

    #print(intersections)

    """
    for intersection in intersections:
        if isinstance(intersection, Interval):
            print(intersection.to_string())
        else:
            print(intersection)

    sys.exit()
    """

    intersection_geom = None

    #print('>>>>>>>>>')

    # disjoint
    if op == Operation.Disjoint.value:
        # get complementary

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
    elif op == STOperation.Intersection.value:
        N = len(intersections)

        if N > 0:
            geoms = []
            for intersection in intersections:
                if isinstance(intersection, Interval):
                    """
                    t = intersection.x
                    reg = get_region_at(msegs, t)

                    x0, y0 = mp.at(t)

                    p0 = reg.intersection(shapely.geometry.Point(x0, y0))

                    t = (intersection.x + intersection.y) / 2
                    reg = get_region_at(msegs, t)

                    x1, y1 = mp.at(t)

                    p1 = reg.intersection(shapely.geometry.Point(x1, y1))

                    t = intersection.y
                    reg = get_region_at(msegs, t)

                    x2, y2 = mp.at(t)

                    p2 = reg.intersection(shapely.geometry.Point(x2, y2))

                    if p0.geom_type == 'Point':
                        x0 = p0.x
                        y0 = p0.y

                    if p1.geom_type == 'Point':
                        x1 = p1.x
                        y1 = p1.y

                    if p2.geom_type == 'Point':
                        x2 = p2.x
                        y2 = p2.y

                    #print(list(p0.geoms), list(p1.geoms), list(p2.geoms))

                    geoms += [LineString(((x0, y0), (x1, y1)))]
                    geoms += [LineString(((x1, y1), (x2, y2)))]
                    """

                    if p_linear_traj:
                        dtt = intersection.y - intersection.x
                        K = 25
                        n = K - 1
                        x0, y0 = mp.at(intersection.x)

                        for j in range(1, K):
                            t = intersection.x + dtt * (float(j) / n)

                            #x0, y0 = mp.at(intersection.x)
                            x1, y1 = mp.at(t)
                            #x2, y2 = mp.at(intersection.y)
                            geoms += [LineString(((x0, y0), (x1, y1)))]

                            x0 = x1
                            y0 = y1
                    else:
                        x0, y0 = mp.at(intersection.x)
                        x1, y1 = mp.at(intersection.y)
                        geoms += [LineString(((x0, y0), (x1, y1)))]

                    #geoms += [LineString(((x0, y0), (x1, y1)))]
                    #geoms += [LineString(((x1, y1), (x2, y2)))]
                else:
                    """
                    t = intersection
                    reg = get_region_at(msegs, t)
                    x0, y0 = mp.at(t)

                    p0 = reg.intersection(shapely.geometry.Point(x0, y0))

                    geoms += [LineString(((p0.x, p0.y), (p0.x, p0.y)))]
                    """

                    x0, y0 = mp.at(intersection)

                    x1 = x0
                    y1 = y0

                    geoms += [LineString(((x0, y0), (x1, y1)))]

            intersection_geom = GeometryCollection(geoms)
        else:
            intersection_geom = GeometryCollection()
    """
    elif op == STOperation.Intersection2.value:
        N = len(intersections)

        if N > 0:
            geoms = []
            for intersection in intersections:
                if isinstance(intersection, Interval):
                    x0, y0 = mp.at(intersection.x)
                    x1, y1 = mp.at(intersection.y)
                else:
                    x0, y0 = mp.at(intersection)

                    x1 = x0
                    y1 = y0

                geoms += [LineString(((x0, y0), (x1, y1)))]

            intersection_geom = GeometryCollection(geoms)
        else:
            intersection_geom = GeometryCollection()
    """

    #print('>>>>>>>>>')

    end_exec_time = time.time()
    exec_time = end_exec_time - begin_exec_time

    day, hour, minutes, seconds = seconds_to_time(int(exec_time))
    #print('{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0))

    get_samples_for_out(msegs, mp, interval, n_samples, intersections)
	
    #get_samples_for_viz_2(msegs, mp, interval, n_samples, intersections)

    sday, shour, sminutes, sseconds = seconds_to_time(int(solver_exec_time))

    #print('>>>>>>>>>')

    if print_intersection_information:
        print(get_intersection_information(intersections, msegs, mp, op))

    if print_solver_execution_time:
        #print('TET: ' + '{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0) + ', SET: ' + '{:0>2}'.format(sseconds, precision_0) + 'sec, NE: ' + str(solver_exec_times))
        print('N: ' + str(len(msegs)) + ', ' + format(exec_time, precision) + ' : ' + format(solver_exec_time, precision) + ', ' + format((solver_exec_time * 100) / exec_time, precision) + '%, TET: ' + '{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0) + ', SET: ' + '{:0>2}'.format(sseconds, precision_0) + ' Sec, NE: ' + str(solver_exec_times))
        #print(str(exec_time) + ' ' + str(solver_exec_time))
        #print('TET: ' + '{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0) + ', SET: ' + format(solver_exec_time, precision) + 'sec, NE: ' + str(solver_exec_times))
        #print('Solver Exec. Time: ' + format(solver_exec_time, precision) + 'sec, NE: ' + str(solver_exec_times))

    if op == STOperation.Intersection.value:
        print(intersection_geom.wkt)

def intersections_tests(MS, mp, initial_state, final_state, op = 1, p_linear_traj = False):
    global begin_exec_time
    global precision_0

    msegs = []

    for ms in MS:
        msegs += [create_moving_segment([ms], pass_through_control_points)]

    intersections = None

    if p_linear_traj:
        for ms in msegs:    
            intersections = get_intersections_4(ms, mp, interval, intersections)
    else:
        for ms in msegs:    
            intersections = get_intersections_3(ms, mp, interval, intersections)

    if initial_state == State.Inside or initial_state == State.Touch:# or initial_state == State.Intersect:
        intersections = [interval.begin()] + intersections

    if final_state == State.Inside or final_state == State.Touch:# or final_state == State.Intersect:
        intersections += [interval.end()]

    intersections = process_intersections(intersections, mp, msegs, initial_state, final_state)

    intersection_geom = None

    # disjoint
    if op == Operation.Disjoint.value:
        # get complementary

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
    elif op == STOperation.Intersection.value:
        N = len(intersections)

        if N > 0:
            geoms = []
            for intersection in intersections:
                if isinstance(intersection, Interval):
                    if p_linear_traj:
                        dtt = intersection.y - intersection.x
                        K = 25
                        n = K - 1
                        x0, y0 = mp.at(intersection.x)

                        for j in range(1, K):
                            t = intersection.x + dtt * (float(j) / n)

                            #x0, y0 = mp.at(intersection.x)
                            x1, y1 = mp.at(t)
                            #x2, y2 = mp.at(intersection.y)
                            geoms += [LineString(((x0, y0), (x1, y1)))]

                            x0 = x1
                            y0 = y1
                    else:
                        x0, y0 = mp.at(intersection.x)
                        x1, y1 = mp.at(intersection.y)
                        geoms += [LineString(((x0, y0), (x1, y1)))]

                    #geoms += [LineString(((x0, y0), (x1, y1)))]
                    #geoms += [LineString(((x1, y1), (x2, y2)))]
                else:
                    x0, y0 = mp.at(intersection)

                    x1 = x0
                    y1 = y0

                    geoms += [LineString(((x0, y0), (x1, y1)))]

            intersection_geom = GeometryCollection(geoms)
        else:
            intersection_geom = GeometryCollection()

    end_exec_time = time.time()
    exec_time = end_exec_time - begin_exec_time

    day, hour, minutes, seconds = seconds_to_time(int(exec_time))

    #get_samples_for_out(msegs, mp, interval, n_samples, intersections)

    sday, shour, sminutes, sseconds = seconds_to_time(int(solver_exec_time))

    #if print_intersection_information:
    #print(get_intersection_information(intersections, msegs, mp, op))

    #if print_solver_execution_time:
    #print('N: ' + str(len(msegs)) + ', ' + str(exec_time) + ' : ' + str(solver_exec_time) + ', ' + format((solver_exec_time * 100) / exec_time, precision) + '%, TET: ' + '{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0) + ', SET: ' + '{:0>2}'.format(sseconds, precision_0) + 'sec, NE: ' + str(solver_exec_times))

    #if op == STOperation.Intersection.value:
    #    print(intersection_geom.wkt)

    return exec_time, solver_exec_time, ((solver_exec_time * 100) / exec_time), seconds, sseconds

"""
    polygons:
        are simple
        have the same number of vertices
        have an implicit 1-1 correspondence
"""
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

def get_in_between_observations(p, q, msegs, num_samples):
    i = 0
    t = 0
    n = num_samples - 1
    num_invalid_geoms = 0
    num_complex_geoms = 0
    geoms = []
    
    while i < num_samples:
        t = float(i) / n

        if t == 0:
            geoms += [p]
        elif t == 1:
            geoms += [q]
        else:
            coords = []
            M = 0
            
            for mseg in msegs:
                xi, yi, xf, yf = mseg.at(t)
                
                if xi == None:
                    continue

                _n = len(coords)

                if _n > 1:
                    _xi = coords[_n - 2][0]
                    _yi = coords[_n - 2][1]
                        
                    _xf = coords[_n - 1][0]
                    _yf = coords[_n - 1][1]
                        
                    if _xi == xi and _yi == yi and _xf == xf and _yf == yf:
                        continue

                coords += [[xi, yi]]
                coords += [[xf, yf]]               
            
            g = LineString(coords)
            g = g.simplify(0.000000001)
            
            # >>>>>
            
            _DX = 0.000000001
            _C = g.coords
            _N = len(_C)
            _I = 1
            _Coords = [(_C[0][0], _C[0][1])]
            
            while _I < _N:
                _X0 = _C[_I-1][0]
                _Y0 = _C[_I-1][1]
                
                _X1 = _C[_I][0]
                _Y1 = _C[_I][1]
                
                if _X1 == _X0 and _Y1 == _Y0:
                    pass
                elif _X0 - _DX <= _X1 and _X1 <= _X0 + _DX and _Y0 - _DX <= _Y1 and _Y1 <= _Y0 + _DX:
                    pass
                else:
                    _Coords += [(_C[_I][0], _C[_I][1])]
                
                _I += 1
            
            # >>>>>
            
            _Coords += [_Coords[0]]
            g = Polygon(_Coords)
            
            geoms += [g]
            
            if not g.is_valid:
                num_invalid_geoms += 1
                        
            if not g.is_simple:
                num_complex_geoms += 1
  
        i += 1

    return geoms, num_invalid_geoms, num_complex_geoms

def output_result(geoms, n_obs, num_invalid_geoms, num_complex_geoms):
    print(n_obs)
    print(num_invalid_geoms)
    print(num_complex_geoms)

    if geoms == []:
        print('POLYGON EMPTY')
    else:
        for g in geoms:
            print(g.wkt)

def test_iceberg_mp_int():
    
    #geoms = []
    num_invalid_geoms = 0
    num_complex_geoms = 0
    n_obs = 100

    #p_wkt = 'POLYGON((-1.40690505548705302 0.03329223181257701, -1.53020961775585707 0.38101109741060424, -1.04932182490752157 0.23057953144266341, -1.40690505548705302 0.03329223181257701))'
    #q_wkt = 'POLYGON((-0.38101109741060424 0.22564734895191119, -0.13440197287299638 0.48458692971639949, 0.07028360049321813 0.02342786683107279, -0.38101109741060424 0.22564734895191119))'

    # iceberg 2
    p_wkt = 'POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))'
    q_wkt = 'POLYGON ((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))'

    """
    p_wkt = 'POLYGON ((697.681 676.415, 695.084 647.493, 714.836 620.117, 734.593 592.733, 772.527 563.013, 800.477 562.349, 839.6 561.282, 879.526 569.042, 916.101 589.532, 952.53 610.013, 956.763 630.205, 953.892 638.599, 939.398 642.023, 938.897 656.829, 931.095 663.378, 934.526 673.012, 924.618 674.667, 920.229 680.637, 909.787 679.936, 890.438 673.407, 876.516 673.781, 875.528 697.023, 871.106 721.117, 867.171 722.34, 862.85 745.224, 839.474 738.195, 827.653 733.061, 819.666 735.233, 794.432 726.839, 781.855 721.31, 735.094 711.577, 703.827 693.561, 697.681 676.415))'
    q_wkt = 'POLYGON ((706.106 705.82, 704.55 685.032, 710.33 655.417, 724.48 633.263, 746.481 600.291, 770.084 587.667, 788.026 582.339, 840.604 575.021, 868.554 577.012, 953.618 609.118, 962.56 621.811, 961.576 630.339, 949.76 642.8, 949.76 655.417, 941.277 663.811, 946.59 673.012, 940.02 675.31, 931.381 683.33, 907.728 680.637, 887.071 682.31, 892.305 699.484, 889.345 729.339, 886.113 732.33, 883.855 755.715, 865.944 752.036, 849.125 747.838, 836.506 752.048, 813.365 745.762, 773.376 743.657, 748.205 739.435, 718.763 726.839, 714.58 714.223, 706.106 705.82))'
    """
    p = loads(p_wkt)
    q = loads(q_wkt)
	
    msegs = get_msegs_simple_polygons_with_corr(p, q)

    # >>>
    coords = []
    t = 0.5

    for mseg in msegs:
        xi, yi, xf, yf = mseg.at(t)
                
        if xi == None:
            continue

        """
        _n = len(coords)

        if _n > 1:
            _xi = coords[_n - 2][0]
            _yi = coords[_n - 2][1]
                        
            _xf = coords[_n - 1][0]
            _yf = coords[_n - 1][1]
                        
            if _xi == xi and _yi == yi and _xf == xf and _yf == yf:
                continue
        """

        coords += [[xi, yi]]
        coords += [[xf, yf]]               
            
    g = Polygon(coords)
    g = g.simplify(0.000001)
            
    if not g.is_valid:
        print('Invalid Observation.')
        sys.exit()
                        
    if not g.is_simple:
        print('Complex Observation.')
        sys.exit()

    g1_coords = p.exterior.coords
    g2_coords = g.exterior.coords
    g3_coords = q.exterior.coords

    """
    print(p.wkt + ';')
    print(g.wkt + ';')
    print(q.wkt + ';')
    sys.exit()
    """

    #print(g1_coords[0][0], S(g1_coords[0][0]))

    """
    a = str(S(g1_coords[0][0])) + ',' + str(S(g1_coords[0][1])) + ',' + str(S(g2_coords[0][0])) + ',' + str(S(g2_coords[0][1])) + ',' + str(S(g3_coords[0][0])) + ',' + str(S(g3_coords[0][1])) + '#'
    b = str(S(g1_coords[1][0])) + ',' + str(S(g1_coords[1][1])) + ',' + str(S(g2_coords[1][0])) + ',' + str(S(g2_coords[1][1])) + ',' + str(S(g3_coords[1][0])) + ',' + str(S(g3_coords[1][1])) + '#'
    c = str(S(g1_coords[2][0])) + ',' + str(S(g1_coords[2][1])) + ',' + str(S(g2_coords[2][0])) + ',' + str(S(g2_coords[2][1])) + ',' + str(S(g3_coords[2][0])) + ',' + str(S(g3_coords[2][1])) + '#'
    """

    MS = []
    N = len(g1_coords) - 1
    i = 1

    prev = str(g1_coords[0][0]) + ',' + str(g1_coords[0][1]) + ',' + str(g2_coords[0][0]) + ',' + str(g2_coords[0][1]) + ',' + str(g3_coords[0][0]) + ',' + str(g3_coords[0][1]) + '#'

    t0 = 1000
    t1 = 2000

    while i < N:
        curr = str(g1_coords[i][0]) + ',' + str(g1_coords[i][1]) + ',' + str(g2_coords[i][0]) + ',' + str(g2_coords[i][1]) + ',' + str(g3_coords[i][0]) + ',' + str(g3_coords[i][1]) + '#'

        MS += [prev + curr + '1000,2000:1000,2000']
        prev = curr
        i += 1

    curr = str(g1_coords[0][0]) + ',' + str(g1_coords[0][1]) + ',' + str(g2_coords[0][0]) + ',' + str(g2_coords[0][1]) + ',' + str(g3_coords[0][0]) + ',' + str(g3_coords[0][1]) + '#'
    MS += [prev + curr + '1000,2000:1000,2000']

    """
    a = str(g1_coords[0][0]) + ',' + str(g1_coords[0][1]) + ',' + str(g2_coords[0][0]) + ',' + str(g2_coords[0][1]) + ',' + str(g3_coords[0][0]) + ',' + str(g3_coords[0][1]) + '#'
    b = str(g1_coords[1][0]) + ',' + str(g1_coords[1][1]) + ',' + str(g2_coords[1][0]) + ',' + str(g2_coords[1][1]) + ',' + str(g3_coords[1][0]) + ',' + str(g3_coords[1][1]) + '#'
    c = str(g1_coords[2][0]) + ',' + str(g1_coords[2][1]) + ',' + str(g2_coords[2][0]) + ',' + str(g2_coords[2][1]) + ',' + str(g3_coords[2][0]) + ',' + str(g3_coords[2][1]) + '#'

    s1 = a + b + '1000,2000:1000,2000'
    s2 = b + c + '1000,2000:1000,2000'
    s3 = a + c + '1000,2000:1000,2000'
    """

    #p = '16,-5#20,11#1000,2000'
    p = '755,489#895,774#1000,2000'

    #print('')
    #print(s1, s2, s3)
    #print('')

    #test_mr_mp(s1, s2, s3, p1)
    #test_mr_mp_2(s1, s2, s3, p1)
    test_mr_mp_2(MS, p)

    """
    geoms, num_invalid_geoms, num_complex_geoms = get_in_between_observations(p, q, msegs, n_obs)
    output_result(geoms, n_obs, num_invalid_geoms, num_complex_geoms)
    
	-1.40690505549,0.0332922318126,-0.893958076449,0.129469790382,-0.381011097411,0.225647348952#-1.53020961776,0.381011097411,-0.832305795314,0.432799013564,-0.134401972873,0.484586929716#1000,2000:1000,2000
	-1.53020961776,0.381011097411,-0.832305795314,0.432799013564,-0.134401972873,0.484586929716#-1.04932182491,0.230579531443,-0.489519112207,0.127003699137,0.0702836004932,0.0234278668311#1000,2000:1000,2000
	-1.40690505549,0.0332922318126,-0.893958076449,0.129469790382,-0.381011097411,0.225647348952#-1.04932182491,0.230579531443,-0.489519112207,0.127003699137,0.0702836004932,0.0234278668311#1000,2000:1000,2000
	
	"""

    sys.exit()

def get_moving_segs_from_observations(p_wkt, q_wkt, t0, t1):
    global err_msg
    global err_code
	
    p = loads(p_wkt)
    q = loads(q_wkt)

    #print(len(p.exterior.coords))
    #sys.exit()

    # get moving segments from p to q

    msegs = get_msegs_simple_polygons_with_corr(p, q)

    # get moving segments at t = 0.5
	
    coords = []
    t = 0.5

    k = 0
    for mseg in msegs:
        xi, yi, xf, yf = mseg.at(t)

        #if xi == None:
        #    continue

        if k == 0:
            coords += [[xi, yi]]
            k = 1

        coords += [[xf, yf]]               
            
    g = Polygon(coords)
    #print(g.wkt + ';')
    #g = g.simplify(0.000001)
    #print(g.wkt + ';')
    #sys.exit()

    if not g.is_valid:
        err_msg = 'get_moving_segs_from_observations() : Invalid Observation.'
        return None
                        
    if not g.is_simple:
        err_msg = 'get_moving_segs_from_observations() : Non-simple Observation.'
        return None

    g1_coords = p.exterior.coords
    g2_coords = g.exterior.coords
    g3_coords = q.exterior.coords

    MS = []
    N = len(g1_coords) - 1
    i = 1

    prev = str(g1_coords[0][0]) + ',' + str(g1_coords[0][1]) + ',' + str(g2_coords[0][0]) + ',' + str(g2_coords[0][1]) + ',' + str(g3_coords[0][0]) + ',' + str(g3_coords[0][1]) + '#'

    #t0 = 1000
    #t1 = 2000

    #t0_str = str(t0)
    #t1_str = str(t1)

    interval = str(t0) + ',' + str(t1)
    interval = interval + ':' + interval
	
    while i < N:
        curr = str(g1_coords[i][0]) + ',' + str(g1_coords[i][1]) + ',' + str(g2_coords[i][0]) + ',' + str(g2_coords[i][1]) + ',' + str(g3_coords[i][0]) + ',' + str(g3_coords[i][1]) + '#'

        #MS += [prev + curr + '1000,2000:1000,2000']
        MS += [prev + curr + interval]
        prev = curr
        i += 1

    curr = str(g1_coords[0][0]) + ',' + str(g1_coords[0][1]) + ',' + str(g2_coords[0][0]) + ',' + str(g2_coords[0][1]) + ',' + str(g3_coords[0][0]) + ',' + str(g3_coords[0][1]) + '#'
    #MS += [prev + curr + '1000,2000:1000,2000']
    MS += [prev + curr + interval]

    return MS

#--------------------------------------------f-----------------------
# Do work.
#-------------------------------------------------------------------

def print_list_terms(l, last_term):
    print('')

    out = ''

    for term in l:
	    out += term + ' '

    print('(' + out + ') ' + last_term)
    print('')

def simplify():
    s = 'ad4km-ad4ky-ad4tz+ad4vz+4ad3kms-4ad3kmt-2ad3kns+2ad3knt-2ad3ksy+2ad3kty-2ad3stz+2ad3svz+2ad3t2z-2ad3tvz+6ad2kms2-12ad2kmst+6ad2kmt2-6ad2kns2+12ad2knst-6ad2knt2+ad2kos2-2ad2kost+ad2kot2-ad2ks2y+2ad2ksty-ad2kt2y-ad2s2tz+ad2s2vz+2ad2st2z-2ad2stvz-ad2t3z+ad2t2vz+4adkms3-12adkms2t+12adkmst2-4adkmt3-6adkns3+18adkns2t-18adknst2+6adknt3+2adkos3-6adkos2t+6adkost2-2adkot3+akms4-4akms3t+6akms2t2-4akmst3+akmt4-2akns4+8akns3t-12akns2t2+8aknst3-2aknt4+akos4-4akos3t+6akos2t2-4akost3+akot4-2bd3kms+2bd3kmt+2bd3ksy-2bd3kty+2bd3stz-2bd3svz-2bd3t2z+2bd3tvz-6bd2kms2+12bd2kmst-6bd2kmt2+4bd2kns2-8bd2knst+4bd2knt2+2bd2ks2y-4bd2ksty+2bd2kt2y+2bd2s2tz-2bd2s2vz-4bd2st2z+4bd2stvz+2bd2t3z-2bd2t2vz-6bdkms3+18bdkms2t-18bdkmst2+6bdkmt3+8bdkns3-24bdkns2t+24bdknst2-8bdknt3-2bdkos3+6bdkos2t-6bdkost2+2bdkot3-2bkms4+8bkms3t-12bkms2t2+8bkmst3-2bkmt4+4bkns4-16bkns3t+24bkns2t2-16bknst3+4bknt4-2bkos4+8bkos3t-12bkos2t2+8bkost3-2bkot4+cd2kms2-2cd2kmst+cd2kmt2-cd2ks2y+2cd2ksty-cd2kt2y-cd2s2tz+cd2s2vz+2cd2st2z-2cd2stvz-cd2t3z+cd2t2vz+2cdkms3-6cdkms2t+6cdkmst2-2cdkmt3-2cdkns3+6cdkns2t-6cdknst2+2cdknt3+ckms4-4ckms3t+6ckms2t2-4ckmst3+ckmt4-2ckns4+8ckns3t-12ckns2t2+8cknst3-2cknt4+ckos4-4ckos3t+6ckos2t2-4ckost3+ckot4-d4gkr+d4gkx+d4gtw-d4gvw-d4kmx+d4kry-d4mtw+d4mvw+d4rtz-d4rvz+2d3gkqs-2d3gkqt-4d3gkrs+4d3gkrt+2d3gksx-2d3gktx+2d3gstw-2d3gsvw-2d3gt2w+2d3gtvw+2d3hkrs-2d3hkrt-2d3hksx+2d3hktx-2d3hstw+2d3hsvw+2d3ht2w-2d3htvw-2d3kmsx+2d3kmtx+2d3knsx-2d3kntx-2d3kqsy+2d3kqty+2d3krsy-2d3krty-2d3mstw+2d3msvw+2d3mt2w-2d3mtvw+2d3nstw-2d3nsvw-2d3nt2w+2d3ntvw-2d3qstz+2d3qsvz+2d3qt2z-2d3qtvz+2d3rstz-2d3rsvz-2d3rt2z+2d3rtvz-d2fgks2+2d2fgkst-d2fgkt2+d2fks2y-2d2fksty+d2fkt2y+d2fs2tz-d2fs2vz-2d2fst2z+2d2fstvz+d2ft3z-d2ft2vz+6d2gkqs2-12d2gkqst+6d2gkqt2-6d2gkrs2+12d2gkrst-6d2gkrt2+d2gks2x-2d2gkstx+d2gkt2x+d2gs2tw-d2gs2vw-2d2gst2w+2d2gstvw+d2gt3w-d2gt2vw-4d2hkqs2+8d2hkqst-4d2hkqt2+6d2hkrs2-12d2hkrst+6d2hkrt2-2d2hks2x+4d2hkstx-2d2hkt2x-2d2hs2tw+2d2hs2vw+4d2hst2w-4d2hstvw-2d2ht3w+2d2ht2vw-d2klrs2+2d2klrst-d2klrt2+d2kls2x-2d2klstx+d2klt2x-d2kms2x+2d2kmstx-d2kmt2x+2d2kns2x-4d2knstx+2d2knt2x-d2kos2x+2d2kostx-d2kot2x-2d2kqs2y+4d2kqsty-2d2kqt2y+d2krs2y-2d2krsty+d2krt2y+d2ls2tw-d2ls2vw-2d2lst2w+2d2lstvw+d2lt3w-d2lt2vw-d2ms2tw+d2ms2vw+2d2mst2w-2d2mstvw-d2mt3w+d2mt2vw+2d2ns2tw-2d2ns2vw-4d2nst2w+4d2nstvw+2d2nt3w-2d2nt2vw-d2os2tw+d2os2vw+2d2ost2w-2d2ostvw-d2ot3w+d2ot2vw-2d2qs2tz+2d2qs2vz+4d2qst2z-4d2qstvz-2d2qt3z+2d2qt2vz+d2rs2tz-d2rs2vz-2d2rst2z+2d2rstvz+d2rt3z-d2rt2vz-2dfgks3+6dfgks2t-6dfgkst2+2dfgkt3+2dfhks3-6dfhks2t+6dfhkst2-2dfhkt3+6dgkqs3-18dgkqs2t+18dgkqst2-6dgkqt3-4dgkrs3+12dgkrs2t-12dgkrst2+4dgkrt3-8dhkqs3+24dhkqs2t-24dhkqst2+8dhkqt3+6dhkrs3-18dhkrs2t+18dhkrst2-6dhkrt3+2dklqs3-6dklqs2t+6dklqst2-2dklqt3-2dklrs3+6dklrs2t-6dklrst2+2dklrt3-fgks4+4fgks3t-6fgks2t2+4fgkst3-fgkt4+2fhks4-8fhks3t+12fhks2t2-8fhkst3+2fhkt4-fkls4+4fkls3t-6fkls2t2+4fklst3-fklt4+2gkqs4-8gkqs3t+12gkqs2t2-8gkqst3+2gkqt4-gkrs4+4gkrs3t-6gkrs2t2+4gkrst3-gkrt4-4hkqs4+16hkqs3t-24hkqs2t2+16hkqst3-4hkqt4+2hkrs4-8hkrs3t+12hkrs2t2-8hkrst3+2hkrt4+2klqs4-8klqs3t+12klqs2t2-8klqst3+2klqt4-klrs4+4klrs3t-6klrs2t2+4klrst3-klrt4'
    s = s.replace('-', ' - ')
    s = s.replace('+', ' + ')

    s = s.split(' ')
    _s = []

    for e in s:
        e = e.strip()
        if len(e) == 0:
            continue
        elif len(e) == 1:
            _s += [e]
        else:
            i = 1
            n = len(e)
            _e = e[0]

            if e[:2].isdigit():
                _e += e[1]
                _e += '*'
                _e += e[2]
                i = 3
            elif e[:1].isdigit():
                _e += '*'
                _e += e[1]
                i = 2

            while i < n:
                if e[i].isdigit():
                    _e += '**'
                    _e += e[i]
                else:
                    _e += '*'
                    _e += e[i]

                i += 1

            _s += [_e]

    s = _s

    terms = []
    terms += [s[0]]

    n = len(s)
    i = 1

    while i < n - 1:
        terms += [s[i] + ' ' + s[i+1]]
        i += 2

    t0 = []
    t1 = []
    t2 = []
    t3 = []
    t4 = []

    for term in terms:
        if term.find('*t^4') != - 1:
            t4 += [term.replace('*t^4', '')]
        elif term.find('*t^3') != - 1:
            t3 += [term.replace('*t^3', '')]
        elif term.find('*t^2') != - 1:
            t2 += [term.replace('*t^2', '')]
        elif term.find('*t') != - 1:
            t1 += [term.replace('*t', '')]
        else:
            t0 += [term]

    last_term = ' / (d**4*k)'
    print_list_terms(t0, last_term)
    print_list_terms(t1, last_term)
    print_list_terms(t2, last_term)
    print_list_terms(t3, last_term)
    print_list_terms(t4, last_term)

    """
    print('')

    out = ''

    for term in t0:
	    out += term + ' '

    print('(' + out + ') / (d^4*k)')
    print('')

    out = ''

    for term in t1:
	    out += term + ' '

    print('t(' + out + ') / (d^4*k)')
    print('')

    out = ''

    for term in t2:
	    out += term + ' '

    print('t^2(' + out + ') / (d^4*k)')
    print('')

    out = ''

    for term in t3:
	    out += term + ' '

    print('t^3(' + out + ') / (d^4*k)')
    print('')

    out = ''

    for term in t4:
	    out += term + ' '

    print('t^4(' + out + ') / (d^4*k)')
    print('')
    """

    sys.exit()

def simplify_2(s, last_term):
    s = s.replace('-', ' - ')
    s = s.replace('+', ' + ')

    s = s.split(' ')
    _s = []

    #print(s)

    for e in s:
        e = e.strip()
        if len(e) == 0:
            continue
        elif len(e) == 1:
            _s += [e]
        else:
            i = 1
            n = len(e)
            _e = e[0]

            if e[:2].isdigit():
                _e += e[1]
                _e += '*'
                _e += e[2]
                i = 3
            elif e[:1].isdigit():
                _e += '*'
                _e += e[1]
                i = 2

            while i < n:
                if e[i].isdigit():
                    _e += '**'
                    _e += e[i]
                else:
                    _e += '*'
                    _e += e[i]

                i += 1

            _s += [_e]

    s = _s
    #print(s)
    terms = []
    i = 1
    if s[0] == '-' or s[0] == '+':
        terms += [s[0] + s[1]]
        i = 2
    else:
        terms += [s[0]]

    n = len(s)


    while i < n - 1:
        terms += [s[i] + ' ' + s[i+1]]
        i += 2

    t0 = []
    t1 = []
    t2 = []
    t3 = []
    t4 = []

    for term in terms:
        if term.find('*t**4') != - 1:
            t4 += [term.replace('*t**4', '')]
        elif term.find('*t**3') != - 1:
            t3 += [term.replace('*t**3', '')]
        elif term.find('*t**2') != - 1:
            t2 += [term.replace('*t**2', '')]
        elif term.find('*t') != - 1:
            t1 += [term.replace('*t', '')]
        else:
            t0 += [term]

    print_list_terms(t0, last_term)
    print_list_terms(t1, last_term)
    print_list_terms(t2, last_term)
    print_list_terms(t3, last_term)
    print_list_terms(t4, last_term)

    sys.exit()

#-------------------------------------------------------------------
# Direction test.
#-------------------------------------------------------------------
def direction(p, q, r):
    signed_area = ((q.x - p.x) * (r.y - p.y)) - ((q.y - p.y) * (r.x - p.x))

    if signed_area > 0:
        return 1
    elif signed_area < 0:
        return -1

    return 0

def dir(px, py, qx, qy, rx, ry):
    signed_area = ((qx - px) * (ry - py)) - ((qy - py) * (rx - px))

    if signed_area > 0:
        return 1
    elif signed_area < 0:
        return -1

    return 0

def on_segment(p, q, r):
    if min(p.x, q.x) <= r.x <= max(p.x, q.x) and min(p.y, q.y) <= r.y <= max(p.y, q.y):
        return True

    return False

def on_segment(px, py, qx, qy, rx, ry):
    if min(px, qx) <= rx <= max(px, qx) and min(py, qy) <= ry <= max(py, qy):
        return True

    return False

def on_segment_with_eps(px, py, qx, qy, rx, ry, epsilon):
    if min(px, qx) - epsilon <= rx <= max(px, qx) + epsilon and min(py, qy) - epsilon <= ry <= max(py, qy) + epsilon:
        return True

    return False

def get_valid_roots(msu1, msu2, roots, op):
    valid_roots = []

    if op == 1:
        for t in roots:
            Ax, Ay, Bx, By = msu1.at(t)
            Cx, Cy, Dx, Dy = msu2.at(t)

            if on_segment(Ax, Ay, Bx, By, Cx, Cy):
                valid_roots += [t]
    elif op == 2:
        for t in roots:
            Ax, Ay, Bx, By = msu1.at(t)
            Cx, Cy, Dx, Dy = msu2.at(t)

            if on_segment(Ax, Ay, Bx, By, Dx, Dy):
                valid_roots += [t]
    elif op == 3:
        for t in roots:
            Ax, Ay, Bx, By = msu1.at(t)
            Cx, Cy, Dx, Dy = msu2.at(t)

            if on_segment(Cx, Cy, Dx, Dy, Ax, Ay):
                valid_roots += [t]
    elif op == 4:
        for t in roots:
            Ax, Ay, Bx, By = msu1.at(t)
            Cx, Cy, Dx, Dy = msu2.at(t)

            if on_segment(Cx, Cy, Dx, Dy, Bx, By):
                valid_roots += [t]

    return valid_roots

def get_msegs_intersections(ms1, ms2, i, prev_it = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon

    s = []

    #if not ms1.i.intersects(i) or not ms2.i.intersects(i) or not ms1.i.intersects(ms2.i):
    #    return s

    ms1_it = 0
    ms2_it = 0

    n_units_ms1 = len(ms1.units)
    n_units_ms2 = len(ms2.units)

    # iterate the units of the objects.
    while ms1_it < n_units_ms1 and ms2_it < n_units_ms2:
        msu1 = ms1.units[ms1_it]
        msu2 = ms2.units[ms2_it]

        # are the units within the interval exausted?
        if msu1.i.x >= i.y or msu2.i.x >= i.y:
            break

        # find two units whose intervals intersect.
        it0 = msu1.i.intersection(i)
        if it0 is None:
            ms1_it += 1
            continue

        it1 = msu2.i.intersection(i)
        if it1 is None:
            ms2_it += 1
            continue

        it = it0.intersection(it1)

        # found an intersection.
        if it != None:

            n_it_ms1 = len(msu1.c0.intervals)
            n_it_ms2 = len(msu2.c0.intervals)

            idx1 = 0
            idx2 = 0
            while idx1 < n_it_ms1 and idx2 < n_it_ms2:
                it1 = msu1.c0.intervals[idx1].intersection(it)
                if it1 is None:
                    idx1 += 1
                    continue

                it2 = msu2.c0.intervals[idx2].intersection(it)
                if it2 is None:
                    idx2 += 1
                    continue

                it0 = it1.intersection(it2)
                if it0 != None:
                    # check collinearity
                    #col = collinear(msu1.c0.curves[idx].cp0, msu1.c0.curves[idx].cp1, msu1.c0.curves[idx].cp2, msu1.c1.curves[idx].cp0, msu1.c1.curves[idx].cp1, msu1.c1.curves[idx].cp2, msu2.p[0], msu2.p[1])

                    col = 0

                    # msu1
                    dt = msu1.c0.intervals[idx1].y - msu1.c0.intervals[idx1].x

                    msu1_dt = dt
                    msu1_t0 = msu1.c0.intervals[idx1].x
                    # Ax
                    c0_cp0_x = msu1.c0.curves[idx1].cp0.x
                    c0_cp1_x = msu1.c0.curves[idx1].cp1.x
                    c0_cp2_x = msu1.c0.curves[idx1].cp2.x
                    # Ay
                    c0_cp0_y = msu1.c0.curves[idx1].cp0.y
                    c0_cp1_y = msu1.c0.curves[idx1].cp1.y
                    c0_cp2_y = msu1.c0.curves[idx1].cp2.y
                    # Bx
                    c1_cp0_x = msu1.c1.curves[idx1].cp0.x
                    c1_cp1_x = msu1.c1.curves[idx1].cp1.x
                    c1_cp2_x = msu1.c1.curves[idx1].cp2.x
                    # By
                    c1_cp0_y = msu1.c1.curves[idx1].cp0.y
                    c1_cp1_y = msu1.c1.curves[idx1].cp1.y
                    c1_cp2_y = msu1.c1.curves[idx1].cp2.y

                    # msu2
                    dt = msu2.c0.intervals[idx2].y - msu2.c0.intervals[idx2].x

                    msu2_dt = dt
                    msu2_t0 = msu2.c0.intervals[idx2].x
                    # Cx
                    c2_cp0_x = msu2.c0.curves[idx2].cp0.x
                    c2_cp1_x = msu2.c0.curves[idx2].cp1.x
                    c2_cp2_x = msu2.c0.curves[idx2].cp2.x
                    # Cy
                    c2_cp0_y = msu2.c0.curves[idx2].cp0.y
                    c2_cp1_y = msu2.c0.curves[idx2].cp1.y
                    c2_cp2_y = msu2.c0.curves[idx2].cp2.y
                    # Dx
                    c3_cp0_x = msu2.c1.curves[idx2].cp0.x
                    c3_cp1_x = msu2.c1.curves[idx2].cp1.x
                    c3_cp2_x = msu2.c1.curves[idx2].cp2.x
                    # Dy
                    c3_cp0_y = msu2.c1.curves[idx2].cp0.y
                    c3_cp1_y = msu2.c1.curves[idx2].cp1.y
                    c3_cp2_y = msu2.c1.curves[idx2].cp2.y

                    # >

                    done = False

                    if col == 0:
                        """
                        t = Symbol('t')

                        T = (t - msu1_t0) / msu1_dt
                        Ax, Ay = msu1.c0.curves[idx1].at(T)
                        Bx, By = msu1.c1.curves[idx1].at(T)

                        T = (t - msu2_t0) / msu2_dt
                        Cx, Cy = msu2.c0.curves[idx2].at(T)
                        Dx, Dy = msu2.c1.curves[idx2].at(T)

                        # first test
                        
                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) < 0
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '<')

                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) > 0
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '>')

                        f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) < 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '<')

                        f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) > 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '>')

                        # >>>

                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '=')

                        f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '=')

                        # second test

                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) < 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '<')

                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) > 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '>')

                        f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx))) < 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '<')

                        f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx))) > 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '>')

                        # >>>

                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '=')

                        f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '=')

                        sys.exit()
                        ###
                        """

                        """
							1679.03 - 1716.60

							{999.999999, 1679.02756239533}
							[1000.0, 1679.02756239533]
							{1679.02756239533, 2000.000001}
							[1679.02756239533, 2000.0]
							{999.999999, 1716.59518563388}
							[1000.0, 1716.59518563388]
							{1716.59518563388, 2000.000001}
							[1716.59518563388, 2000.0]
							[1679.02756239533]
							[1716.59518563388]
							{1678.42146203489, 2000.000001}
							[1678.42146203489, 2000.0]
							{999.999999, 1678.42146203489}
							[1000.0, 1678.42146203489]
							{1731.35403314197, 2000.000001}
							[1731.35403314197, 2000.0]
							{999.999999, 1731.35403314197}
							[1000.0, 1731.35403314197]
							[1678.42146203489]
							[1731.35403314197]
                        """

                        """
                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) + (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) + (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) + (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r)

                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) + (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r)

                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) + (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r)

                        sys.exit()
                        """

                        """
                        f = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By)
                        p, q, r
                        signed_area = ((q.x - p.x) * (r.y - p.y)) - ((q.y - p.y) * (r.x - p.x))
                        A, B, C
                        A, B, D
						
						(3520.9999999999995, -8.263, 0.005897, -1.428e-06, 6e-11)
						[19000.16166467  2317.27192095  1697.2836968    785.28271758]
						[1697.28369680100]

						D:\java>python tests.py
						[1697.28369680099]
						{1697.28369680099}
						[1697.28369680099]

						D:\java>python tests.py
						{1087.83819634203, 1680.60010160353}
						[1087.83819634203, 1680.60010160353]				
                        """

                        """
                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) + (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) + (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) + (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r)
                        """

                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) < 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r)

                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) > 0
                        #exec_time, r1 = get_solutions(f, t, it)
                        #r += r1

                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) < 0
                        #exec_time, r1 = get_solutions(f, t, it)
                        #r += r1

                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) > 0
                        #exec_time, r1 = get_solutions(f, t, it)
                        #r += r1
                        #sys.exit()

                        """
                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) < 0
                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                        exec_time, r = get_solutions(f, t, it)

                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) > 0
                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        exec_time, r1 = get_solutions(f, t, it)
                        r += r1

                        f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx))) < 0
                        exec_time, r1 = get_solutions(f, t, it)
                        r += r1

                        f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx))) > 0
                        exec_time, r1 = get_solutions(f, t, it)
                        r += r1
                        """

                        """
                        {999.999999, 1679.02756239533}
                        {1679.02756239533, 2000.000001}
                        {999.999999, 1716.59518563388}
                        {1716.59518563388, 2000.000001}
						
						{1678.42146203489, 2000.000001}
						{999.999999, 1678.42146203489}
						{1731.35403314197, 2000.000001}
						{999.999999, 1731.35403314197}						
                        """

                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                        exec_time, r1 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        exec_time, r2 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx)))
                        exec_time, r3 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r4 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        print(r1, r2, r3, r4)

                        r1 = get_valid_roots(msu1, msu2, r1, 1)
                        r2 = get_valid_roots(msu1, msu2, r2, 2)
                        r3 = get_valid_roots(msu1, msu2, r3, 3)
                        r4 = get_valid_roots(msu1, msu2, r4, 4)

                        print(r1, r2, r3, r4)
                        sys.exit()

                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                        #exec_time, r1 = get_solutions(f, t, it)
                        #exec_time, r1 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        #exec_time, r2 = get_solutions(f, t, it)
                        #exec_time, r2 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #print(r1, r2)


                        r0 = []
                        if len(r1) == 1 and len(r2) == 1:
                            r0 = r1 + r2
                            r0.sort()
                        elif len(r1) == 1 and len(r2) == 0:
                            t = r1[0]
                            Ax, Ay, Bx, By = msu1.at(t)
                            Cx, Cy, Dx, Dy = msu2.at(t)

                            if on_segment(Ax, Ay, Bx, By, Cx, Cy):
                                r0 = r1
                        elif len(r1) == 0 and len(r2) == 1:
                            t = r2[0]
                            Ax, Ay, Bx, By = msu1.at(t)
                            Cx, Cy, Dx, Dy = msu2.at(t)

                            if on_segment(Ax, Ay, Bx, By, Dx, Dy):
                                r0 = r2

                        #f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx)))
                        #exec_time, r1 = get_solutions(f, t, it)
                        exec_time, r1 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        #exec_time, r2 = get_solutions(f, t, it)
                        exec_time, r2 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #print(r1, r2)

                        """
						([], [1924.16039889982])
						([], [1735.84203882648])						
                        """

                        r = []
                        if len(r1) == 1 and len(r2) == 1:
                            r = r1 + r2
                            r.sort()
                        elif len(r1) == 1 and len(r2) == 0:
                            t = r1[0]
                            Ax, Ay, Bx, By = msu1.at(t)
                            Cx, Cy, Dx, Dy = msu2.at(t)

                            if on_segment(Cx, Cy, Dx, Dy, Ax, Ay):
                                r = r1
                        elif len(r1) == 0 and len(r2) == 1:
                            t = r2[0]
                            Ax, Ay, Bx, By = msu1.at(t)
                            Cx, Cy, Dx, Dy = msu2.at(t)

                            if on_segment(Cx, Cy, Dx, Dy, Bx, By):
                                r = r2

                        if len(r0) == 2 and len(r) == 2:
                            i0 = Interval(r0[0], r0[1], True, True)
                            i1 = Interval(r[0], r[1], True, True)

                            _it = i0.intersection(i1)

                            if _it == None:
                                r = []
                            else:
                                #r = [_it.x, _it.y]
                                r = [_it]
                        else:
                            r = r + r0
                            r.sort()


                        #print(i0.to_string(), i1.to_string(), _it.to_string())

                        #'INTERVAL [1679.02756239533, 1716.59518563388]', 
                        #'INTERVAL [1678.42146203489, 1731.35403314197]', 
                        #'INTERVAL [1679.02756239533, 1716.59518563388]')

                        #r = [1679.02756239533, 1716.59518563388]
                        #print(r)
                        # it or it0?

                        """
						D:\java>python tests.py
						[1087.83819634203, 1680.60010160353]
						[1675.77778703300]

						D:\java>python tests.py
						[1087.83819634203, 1680.60010160353]
						[1682.29230710688]
						
                        exec_time, r = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)
                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        print(r)						
                        sys.exit()
                        """

                        """
                        exec_time, r2 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        solver_exec_time += exec_time
                        solver_exec_times += 1
                        """

                    else:
                        pass

                    if not done:
                        r.sort()

                        for root in r:
                            n = len(s)

                            if n == 0:
                                s += [root]
                            else:
                                prev = s[n-1]

                                if isinstance(prev, Interval):
                                    if not prev.contains(root):
                                        s += [root]
                                else:
                                    if root != prev:
                                        s += [root]

                if msu1.c0.intervals[idx1].y == msu2.c0.intervals[idx2].y:
                    idx1 += 1
                    idx2 += 1
                elif msu1.c0.intervals[idx1].y < msu2.c0.intervals[idx2].y:
                    idx1 += 1
                else:
                    idx2 += 1

        # Next unit(s).
        if msu1.i.y == msu2.i.y:
            ms1_it += 1
            ms2_it += 1
        elif msu1.i.y < msu2.i.y:
            ms1_it += 1
        else:
            ms2_it += 1

    # sort intersections
	
    if prev_it != None:
        i = 0
        j = 0

        _sorted = []

        n = len(prev_it)
        m = len(s)

        while i < n and j < m:
            x1 = prev_it[i]
            x2 = s[j]

            if isinstance(x1, Interval) and isinstance(x2, Interval):
                ix0 = x1.begin()
                ix1 = x1.end()
                ix2 = x2.begin()
                ix3 = x2.end()

                if ix1 <= ix2:
                    _sorted += [x1]
                    i += 1
                elif ix3 <= ix0:
                    _sorted += [x2]
                    j += 1
                else:
                    print('ERR: Interval overlap. ' + x1.to_string() + ' ' + x2.to_string())
            elif isinstance(x1, Interval):
                ix0 = x1.begin()
                ix1 = x1.end()

                if x2 < ix0:
                    _sorted += [x2]
                    j += 1
                elif x2 > ix1:
                    _sorted += [x1]
                    i += 1
                else:
                    _sorted += [x1]
                    i += 1
                    j += 1
            elif isinstance(x2, Interval):
                ix0 = x2.begin()
                ix1 = x2.end()

                if x1 < ix0:
                    _sorted += [x1]
                    i += 1
                elif x1 > ix1:
                    _sorted += [x2]
                    j += 1
                else:
                    _sorted += [x2]
                    i += 1
                    j += 1
            else:
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

def get_msegs_intersections_2(ms1, ms2, i, prev_it = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon

    s = []

    #if not ms1.i.intersects(i) or not ms2.i.intersects(i) or not ms1.i.intersects(ms2.i):
    #    return s

    ms1_it = 0
    ms2_it = 0

    n_units_ms1 = len(ms1.units)
    n_units_ms2 = len(ms2.units)

    # iterate the units of the objects.
    while ms1_it < n_units_ms1 and ms2_it < n_units_ms2:
        msu1 = ms1.units[ms1_it]
        msu2 = ms2.units[ms2_it]

        # are the units within the interval exausted?
        if msu1.i.x >= i.y or msu2.i.x >= i.y:
            break

        # find two units whose intervals intersect.
        it0 = msu1.i.intersection(i)
        if it0 is None:
            ms1_it += 1
            continue

        it1 = msu2.i.intersection(i)
        if it1 is None:
            ms2_it += 1
            continue

        it = it0.intersection(it1)

        # found an intersection.
        if it != None:

            n_it_ms1 = len(msu1.c0.intervals)
            n_it_ms2 = len(msu2.c0.intervals)

            idx1 = 0
            idx2 = 0
            while idx1 < n_it_ms1 and idx2 < n_it_ms2:
                it1 = msu1.c0.intervals[idx1].intersection(it)
                if it1 is None:
                    idx1 += 1
                    continue

                it2 = msu2.c0.intervals[idx2].intersection(it)
                if it2 is None:
                    idx2 += 1
                    continue

                it0 = it1.intersection(it2)
                if it0 != None:
                    # check collinearity
                    #col = collinear(msu1.c0.curves[idx].cp0, msu1.c0.curves[idx].cp1, msu1.c0.curves[idx].cp2, msu1.c1.curves[idx].cp0, msu1.c1.curves[idx].cp1, msu1.c1.curves[idx].cp2, msu2.p[0], msu2.p[1])

                    col = 0

                    # msu1
                    dt = msu1.c0.intervals[idx1].y - msu1.c0.intervals[idx1].x

                    msu1_dt = dt
                    msu1_t0 = msu1.c0.intervals[idx1].x

                    c0_cp0_x = msu1.c0.curves[idx1].cp0.x
                    c0_cp1_x = msu1.c0.curves[idx1].cp1.x
                    c0_cp2_x = msu1.c0.curves[idx1].cp2.x

                    c0_cp0_y = msu1.c0.curves[idx1].cp0.y
                    c0_cp1_y = msu1.c0.curves[idx1].cp1.y
                    c0_cp2_y = msu1.c0.curves[idx1].cp2.y

                    c1_cp0_x = msu1.c1.curves[idx1].cp0.x
                    c1_cp1_x = msu1.c1.curves[idx1].cp1.x
                    c1_cp2_x = msu1.c1.curves[idx1].cp2.x

                    c1_cp0_y = msu1.c1.curves[idx1].cp0.y
                    c1_cp1_y = msu1.c1.curves[idx1].cp1.y
                    c1_cp2_y = msu1.c1.curves[idx1].cp2.y

                    # msu2
                    dt = msu2.c0.intervals[idx2].y - msu2.c0.intervals[idx2].x

                    msu2_dt = dt
                    msu2_t0 = msu2.c0.intervals[idx2].x

                    c2_cp0_x = msu2.c0.curves[idx2].cp0.x
                    c2_cp1_x = msu2.c0.curves[idx2].cp1.x
                    c2_cp2_x = msu2.c0.curves[idx2].cp2.x

                    c2_cp0_y = msu2.c0.curves[idx2].cp0.y
                    c2_cp1_y = msu2.c0.curves[idx2].cp1.y
                    c2_cp2_y = msu2.c0.curves[idx2].cp2.y

                    c3_cp0_x = msu2.c1.curves[idx2].cp0.x
                    c3_cp1_x = msu2.c1.curves[idx2].cp1.x
                    c3_cp2_x = msu2.c1.curves[idx2].cp2.x

                    c3_cp0_y = msu2.c1.curves[idx2].cp0.y
                    c3_cp1_y = msu2.c1.curves[idx2].cp1.y
                    c3_cp2_y = msu2.c1.curves[idx2].cp2.y

                    # >

                    done = False

                    if col == 0:

                        t = Symbol('t')

                        T = (t - msu1_t0) / msu1_dt
                        Ax, Ay = msu1.c0.curves[idx1].at(T)
                        Bx, By = msu1.c1.curves[idx1].at(T)

                        T = (t - msu2_t0) / msu2_dt
                        Cx, Cy = msu2.c0.curves[idx2].at(T)
                        Dx, Dy = msu2.c1.curves[idx2].at(T)

                        # first test
                        
                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) < 0
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '<')

                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) > 0
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '>')

                        f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) < 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '<')

                        f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) > 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '>')

                        # >>>

                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '=')

                        f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '=')

                        # second test

                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) < 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '<')

                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) > 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '>')

                        f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx))) < 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '<')

                        f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx))) > 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r, '>')

                        # >>>

                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '=')

                        f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r, '=')

                        sys.exit()
                        ###
                        

                        """
							1679.03 - 1716.60

							{999.999999, 1679.02756239533}
							[1000.0, 1679.02756239533]
							{1679.02756239533, 2000.000001}
							[1679.02756239533, 2000.0]
							{999.999999, 1716.59518563388}
							[1000.0, 1716.59518563388]
							{1716.59518563388, 2000.000001}
							[1716.59518563388, 2000.0]
							[1679.02756239533]
							[1716.59518563388]
							{1678.42146203489, 2000.000001}
							[1678.42146203489, 2000.0]
							{999.999999, 1678.42146203489}
							[1000.0, 1678.42146203489]
							{1731.35403314197, 2000.000001}
							[1731.35403314197, 2000.0]
							{999.999999, 1731.35403314197}
							[1000.0, 1731.35403314197]
							[1678.42146203489]
							[1731.35403314197]
                        """

                        """
                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) + (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) + (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) + (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r)

                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) + (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r)

                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) + (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r)

                        sys.exit()
                        """

                        """
                        f = Ax * (By - Cy) + Bx * (Cy - Ay) + Cx * (Ay - By)
                        p, q, r
                        signed_area = ((q.x - p.x) * (r.y - p.y)) - ((q.y - p.y) * (r.x - p.x))
                        A, B, C
                        A, B, D
						
						(3520.9999999999995, -8.263, 0.005897, -1.428e-06, 6e-11)
						[19000.16166467  2317.27192095  1697.2836968    785.28271758]
						[1697.28369680100]

						D:\java>python tests.py
						[1697.28369680099]
						{1697.28369680099}
						[1697.28369680099]

						D:\java>python tests.py
						{1087.83819634203, 1680.60010160353}
						[1087.83819634203, 1680.60010160353]				
                        """

                        """
                        f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) + (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) + (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) + (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r = get_solutions(f, t, it)
                        print(r)
                        """

                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) < 0
                        #exec_time, r = get_solutions(f, t, it)
                        #print(r)

                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax))) > 0
                        #exec_time, r1 = get_solutions(f, t, it)
                        #r += r1

                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) < 0
                        #exec_time, r1 = get_solutions(f, t, it)
                        #r += r1

                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax))) > 0
                        #exec_time, r1 = get_solutions(f, t, it)
                        #r += r1
                        #sys.exit()

                        """
                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) < 0
                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                        exec_time, r = get_solutions(f, t, it)

                        f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx))) > 0
                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        exec_time, r1 = get_solutions(f, t, it)
                        r += r1

                        f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx))) < 0
                        exec_time, r1 = get_solutions(f, t, it)
                        r += r1

                        f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx))) > 0
                        exec_time, r1 = get_solutions(f, t, it)
                        r += r1
                        """

                        """
                        {999.999999, 1679.02756239533}
                        {1679.02756239533, 2000.000001}
                        {999.999999, 1716.59518563388}
                        {1716.59518563388, 2000.000001}
						
						{1678.42146203489, 2000.000001}
						{999.999999, 1678.42146203489}
						{1731.35403314197, 2000.000001}
						{999.999999, 1731.35403314197}						
                        """

                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                        #exec_time, r1 = get_solutions(f, t, it)
                        exec_time, r1 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        #exec_time, r2 = get_solutions(f, t, it)
                        exec_time, r2 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #print(r1, r2)

                        r0 = []
                        if len(r1) == 1 and len(r2) == 1:
                            r0 = r1 + r2
                            r0.sort()
                        elif len(r1) == 1 and len(r2) == 0:
                            t = r1[0]
                            Ax, Ay, Bx, By = msu1.at(t)
                            Cx, Cy, Dx, Dy = msu2.at(t)

                            if on_segment(Ax, Ay, Bx, By, Cx, Cy):
                                r0 = r1
                        elif len(r1) == 0 and len(r2) == 1:
                            t = r2[0]
                            Ax, Ay, Bx, By = msu1.at(t)
                            Cx, Cy, Dx, Dy = msu2.at(t)

                            if on_segment(Ax, Ay, Bx, By, Dx, Dy):
                                r0 = r2

                        #f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx)))
                        #exec_time, r1 = get_solutions(f, t, it)
                        exec_time, r1 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        #exec_time, r2 = get_solutions(f, t, it)
                        exec_time, r2 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #print(r1, r2)

                        """
						([], [1924.16039889982])
						([], [1735.84203882648])						
                        """

                        r = []
                        if len(r1) == 1 and len(r2) == 1:
                            r = r1 + r2
                            r.sort()
                        elif len(r1) == 1 and len(r2) == 0:
                            t = r1[0]
                            Ax, Ay, Bx, By = msu1.at(t)
                            Cx, Cy, Dx, Dy = msu2.at(t)

                            if on_segment(Cx, Cy, Dx, Dy, Ax, Ay):
                                r = r1
                        elif len(r1) == 0 and len(r2) == 1:
                            t = r2[0]
                            Ax, Ay, Bx, By = msu1.at(t)
                            Cx, Cy, Dx, Dy = msu2.at(t)

                            if on_segment(Cx, Cy, Dx, Dy, Bx, By):
                                r = r2

                        if len(r0) == 2 and len(r) == 2:
                            i0 = Interval(r0[0], r0[1], True, True)
                            i1 = Interval(r[0], r[1], True, True)

                            _it = i0.intersection(i1)

                            if _it == None:
                                r = []
                            else:
                                #r = [_it.x, _it.y]
                                r = [_it]
                        else:
                            r = r + r0
                            r.sort()


                        #print(i0.to_string(), i1.to_string(), _it.to_string())

                        #'INTERVAL [1679.02756239533, 1716.59518563388]', 
                        #'INTERVAL [1678.42146203489, 1731.35403314197]', 
                        #'INTERVAL [1679.02756239533, 1716.59518563388]')

                        #r = [1679.02756239533, 1716.59518563388]
                        #print(r)
                        # it or it0?

                        """
						D:\java>python tests.py
						[1087.83819634203, 1680.60010160353]
						[1675.77778703300]

						D:\java>python tests.py
						[1087.83819634203, 1680.60010160353]
						[1682.29230710688]
						
                        exec_time, r = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)
                        solver_exec_time += exec_time
                        solver_exec_times += 1

                        print(r)						
                        sys.exit()
                        """

                        """
                        exec_time, r2 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        solver_exec_time += exec_time
                        solver_exec_times += 1
                        """

                    else:
                        pass

                    if not done:
                        r.sort()

                        for root in r:
                            n = len(s)

                            if n == 0:
                                s += [root]
                            else:
                                prev = s[n-1]

                                if isinstance(prev, Interval):
                                    if not prev.contains(root):
                                        s += [root]
                                else:
                                    if root != prev:
                                        s += [root]

                if msu1.c0.intervals[idx1].y == msu2.c0.intervals[idx2].y:
                    idx1 += 1
                    idx2 += 1
                elif msu1.c0.intervals[idx1].y < msu2.c0.intervals[idx2].y:
                    idx1 += 1
                else:
                    idx2 += 1

        # Next unit(s).
        if msu1.i.y == msu2.i.y:
            ms1_it += 1
            ms2_it += 1
        elif msu1.i.y < msu2.i.y:
            ms1_it += 1
        else:
            ms2_it += 1

    # sort intersections
	
    if prev_it != None:
        i = 0
        j = 0

        _sorted = []

        n = len(prev_it)
        m = len(s)

        while i < n and j < m:
            x1 = prev_it[i]
            x2 = s[j]

            if isinstance(x1, Interval) and isinstance(x2, Interval):
                ix0 = x1.begin()
                ix1 = x1.end()
                ix2 = x2.begin()
                ix3 = x2.end()

                if ix1 <= ix2:
                    _sorted += [x1]
                    i += 1
                elif ix3 <= ix0:
                    _sorted += [x2]
                    j += 1
                else:
                    print('ERR: Interval overlap. ' + x1.to_string() + ' ' + x2.to_string())
            elif isinstance(x1, Interval):
                ix0 = x1.begin()
                ix1 = x1.end()

                if x2 < ix0:
                    _sorted += [x2]
                    j += 1
                elif x2 > ix1:
                    _sorted += [x1]
                    i += 1
                else:
                    _sorted += [x1]
                    i += 1
                    j += 1
            elif isinstance(x2, Interval):
                ix0 = x2.begin()
                ix1 = x2.end()

                if x1 < ix0:
                    _sorted += [x1]
                    i += 1
                elif x1 > ix1:
                    _sorted += [x2]
                    j += 1
                else:
                    _sorted += [x2]
                    i += 1
                    j += 1
            else:
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

def get_msegs_samples_for_viz(MS, i, n_samples, s):
    n = (n_samples - 1)
    k = 0
    dt = i.y - i.x
    eq = False

    J = 0
    T = []
    
    for I in s:
        if isinstance(I, Interval):
            T += [I.x, I.y]
        else:
            T += [I]

    N = len(T)

    for j in range(0, n_samples):
        t = i.x + dt * (float(j) / n)

        #mline = get_mline(MS, t)

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    if J < N and t >= T[J]:
                        mline = get_mline(MS, T[J])
                        #print(T[J], 1)
                        J += 1
                    else:
                        mline = get_mline(MS, t)

                    print(mline.wkt)
                    print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    if J < N and t >= T[J]:
                        mline = get_mline(MS, T[J])
                        #print(T[J], 2)
                        J += 1
                    else:
                        mline = get_mline(MS, t)

                    print(mline.wkt)
                    print(1)
                    k += 1

                    eq = True

        if not eq:
            out = '0'
            if J < N and t >= T[J]:
                mline = get_mline(MS, T[J])
                #print(T[J], 3, t)
                out = '1'
                J += 1
            else:
                mline = get_mline(MS, t)

            print(mline.wkt)
            print(out)
        else:
            eq = False

def get_msegs_intersection_information(MS, intersection_instants):
    add_comma = False
    info = "NI: " + str(len(intersection_instants)) + ": "

    for t in intersection_instants:
        if add_comma:
            info += ", "
        else:
            add_comma = True

        if isinstance(t, Interval):
            P0x, P0y, Qx, Qy = MS[0].at(t.x)
            P1x, P1y, Qx, Qy = MS[0].at(t.y)

            if t.l:
                info += '['
            else:
                info += ']'

            info += 't0: ' + format(t.x, precision) + ", x: " + format(P0x, precision) + ', y: ' + format(P0y, precision)
            info += ', '
            info += 't1: ' + format(t.y, precision) + ", x: " + format(P1x, precision) + ', y: ' + format(P1y, precision)

            if t.r:
                info += ']'
            else:
                info += '['
        else:
            Px, Py, Qx, Qy = MS[0].at(t)
            info += 't: ' + format(t, precision) + ", x: " + format(Px, precision) + ', y: ' + format(Py, precision)

    #info += "}"
    return info

def test_mseg_mseg_int():
    #s1 = '1,2,7,5.5,12,8#7,5,16.5,6.9,25,7#1000,2000:1000,2000'
    #s2 = '1,2,7,5.5,12,8#9,1,11.5,2.5,13,4#1000,2000:1000,2000'
    #s3 = '7,5,16.5,6.9,25,7#9,1,11.5,2.5,13,4#1000,2000:1000,2000'

    #s1 = '1,1,3,3,5,5#1,1,3,3,5,5#1000,2000:1000,2000'
    #s2 = '5,1,3,3,1,5#5,1,3,3,1,5#1000,2000:1000,2000'

    # Tests with Intersection

    # 1 case
    # intersection (both points of a segment intersect the other segment. <no intersection, intersection, no intersection>
    s1 = '1,1,10,-1,20,2#4,7,11,11,18,9#1000,2000:1000,2000'
    s2 = '22,1,15,0,12,-1#19,8,16,9,11,5#1000,2000:1000,2000'

    #s1 = '1,1,7,0,14,1#7,7,9.5,6,12,7#1000,2000:1000,2000'

    # 2 case
    #s1 = '1,1,7,0,14,1#7,7,9,6,10,7#1000,2000:1000,2000'
    #s2 = '10,6,6,5,2,7#8,10,7,9,6,8#1000,2000:1000,2000'

    # 3 case
    #s1 = '1,1,7,0,14,1#7,7,9,6,10,7#1000,2000:1000,2000'
    #s2 = '8,8,12,3,16,2#15,7,16,6,17,5#1000,2000:1000,2000'

    # 3 case
    #s1 = '1,1,3,0,5,1#5,7,6,5,7,7#1000,2000:1000,2000'
    #s2 = '6.4,6.4,3,3,8,2#10,6.5,11,6,12,5.5#1000,2000:1000,2000'

    # special case 1 (100% overlap)
    #s1 = '1,1,2,2,3,3#7,7,9,9,11,11#1000,2000:1000,2000'
    #s2 = '3,3,2,2,1,1#9,9,8,8,7,7#1000,2000:1000,2000'

    # special case 2 (parcial overlap)
    #s1 = '1,1,2,2,3,3#7,7,9,9,11,11#1000,2000:1000,2000'
    #s2 = '3,3,0,0,-3,-3#9,9,5,5,1,1#1000,2000:1000,2000'

    # End Tests WI

    # >>>

    # intersection (in/out)
    #s1 = '1,1,10,-1,20,2#4,7,11,11,18,9#1000,2000:1000,2000'
    #s2 = '22,1,15,0,12,-1#19,-8,16,-9,11,-5#1000,2000:1000,2000'

    # no intersection
    #s1 = '1,1,10,-1,20,2#4,7,11,11,18,9#1000,2000:1000,2000'
    #s2 = '22,0,15,-1,12,-2#19,-8,16,-9,11,-5#1000,2000:1000,2000'

    # intersection (in)
    #s1 = '1,1,10,-1,20,2#4,7,11,11,18,9#1000,2000:1000,2000'
    #s2 = '26,2,24,2.5,23,3#28,8,22,7,17,5#1000,2000:1000,2000'
    
    ms1 = create_moving_segment([s1], pass_through_control_points)
    ms2 = create_moving_segment([s2], pass_through_control_points)
    #ms3 = create_moving_segment([s3], pass_through_control_points)

    """

    """
    """
    print(pass_through_control_points)
    print(ms1.to_string())
    print(ms2.to_string())
    """

    #print(ms1.at(1500))
    #print(ms2.at(1500))

    #sys.exit()

    MS = [ms1, ms2]
    intersections = []



    intersections = get_msegs_intersections(ms1, ms2, interval)
    #intersections = get_intersections(ms2, mp1, interval, intersections)
    #intersections = get_intersections(ms3, mp1, interval, intersections)

    #print(interval.to_string())
    #print(intersections)
    #sys.exit()

	#get_solutions_quartic_dir(a, b, c, g, h, l, r, q, f, m, n, o, w, v, y, x, k, u, s, d, z, p, it):
	
    # rearange
    n = len(intersections)

    if n > 1:
        i = 0
        _intersections = []
        while i < n:
            i0 = intersections[i]
            i1 = intersections[i+1]

            if isinstance(i0, Interval):
                _intersections += [i0]
                i += 1
            elif not isinstance(i1, Interval):
                _intersections += [Interval(i0, i1, True, True)]
                i += 2
            else:
                print('ERR: instant followed by interval in the intersections list.')
                sys.exit()

        if isinstance(intersections[n-1], Interval):
            _intersections += [intersections[n-1]]

        intersections = _intersections

    get_msegs_samples_for_viz(MS, interval, n_samples, intersections)

    if print_intersection_information:
        print(get_msegs_intersection_information(MS, intersections))

    if print_solver_execution_time:
        print("Exec. Time: "+ format(solver_exec_time, precision) + "sec, NI: " + str(solver_exec_times))

    sys.exit()

#def get_solutions_quartic_dir(a, b, c, g, h, l, r, q, f, m, n, o, w, v, y, x, k, u, ww, vv, yy, xx, kk, uu, s, d, z, p, it):
def get_solutions_quartic_dir(a, b, c, g, h, l, r, q, f, m, n, o, w, v, y, x, k, u, s, d, z, p, it):
    global eps

    s_exec_time = time.time()

    """
    a0 = (+2*a*d**4*k*p*z + 2*a*d**4*k*z**2 + a*d**4*m*p**2 - a*d**4*p**2*x - 2*a*d**4*p*x*z - a*d**4*u*z**2 - a*d**4*x*z**2 + 4*a*d**3*k*p*s*z + 4*a*d**3*k*s*z**2 + 4*a*d**3*m*p**2*s - 2*a*d**3*n*p**2*s - 2*a*d**3*p**2*s*x - 4*a*d**3*p*s*x*z - 2*a*d**3*s*u*z**2 - 2*a*d**3*s*x*z**2 + 2*a*d**2*k*p*s**2*z + 2*a*d**2*k*s**2*z**2 + 6*a*d**2*m*p**2*s**2 - 6*a*d**2*n*p**2*s**2 + a*d**2*o*p**2*s**2 - a*d**2*p**2*s**2*x - 2*a*d**2*p*s**2*x*z - a*d**2*s**2*u*z**2 - a*d**2*s**2*x*z**2 + 4*a*d*m*p**2*s**3 - 6*a*d*n*p**2*s**3 + 2*a*d*o*p**2*s**3 + a*m*p**2*s**4 - 2*a*n*p**2*s**4 + a*o*p**2*s**4 - 4*b*d**3*k*p*s*z - 4*b*d**3*k*s*z**2 - 2*b*d**3*m*p**2*s + 2*b*d**3*p**2*s*x + 4*b*d**3*p*s*x*z + 2*b*d**3*s*u*z**2 + 2*b*d**3*s*x*z**2 - 4*b*d**2*k*p*s**2*z - 4*b*d**2*k*s**2*z**2 - 6*b*d**2*m*p**2*s**2 + 4*b*d**2*n*p**2*s**2 + 2*b*d**2*p**2*s**2*x + 4*b*d**2*p*s**2*x*z + 2*b*d**2*s**2*u*z**2 + 2*b*d**2*s**2*x*z**2 - 6*b*d*m*p**2*s**3 + 8*b*d*n*p**2*s**3 - 2*b*d*o*p**2*s**3 - 2*b*m*p**2*s**4 + 4*b*n*p**2*s**4 - 2*b*o*p**2*s**4 + 2*c*d**2*k*p*s**2*z + 2*c*d**2*k*s**2*z**2 + c*d**2*m*p**2*s**2 - c*d**2*p**2*s**2*x - 2*c*d**2*p*s**2*x*z - c*d**2*s**2*u*z**2 - c*d**2*s**2*x*z**2 + 2*c*d*m*p**2*s**3 - 2*c*d*n*p**2*s**3 + c*m*p**2*s**4 - 2*c*n*p**2*s**4 + c*o*p**2*s**4 - d**4*g*p**2*r + d**4*g*p**2*w - 2*d**4*g*p*v*z + 2*d**4*g*p*w*z - 2*d**4*g*v*z**2 + d**4*g*w*z**2 + d**4*g*y*z**2 - 2*d**4*k*p*r*z - 2*d**4*k*r*z**2 - d**4*m*p**2*w + 2*d**4*m*p*v*z - 2*d**4*m*p*w*z + 2*d**4*m*v*z**2 - d**4*m*w*z**2 - d**4*m*y*z**2 + d**4*p**2*r*x + 2*d**4*p*r*x*z + d**4*r*u*z**2 + d**4*r*x*z**2 + 2*d**3*g*p**2*q*s - 4*d**3*g*p**2*r*s + 2*d**3*g*p**2*s*w - 4*d**3*g*p*s*v*z + 4*d**3*g*p*s*w*z - 4*d**3*g*s*v*z**2 + 2*d**3*g*s*w*z**2 + 2*d**3*g*s*y*z**2 + 2*d**3*h*p**2*r*s - 2*d**3*h*p**2*s*w + 4*d**3*h*p*s*v*z - 4*d**3*h*p*s*w*z + 4*d**3*h*s*v*z**2 - 2*d**3*h*s*w*z**2 - 2*d**3*h*s*y*z**2 + 4*d**3*k*p*q*s*z - 4*d**3*k*p*r*s*z + 4*d**3*k*q*s*z**2 - 4*d**3*k*r*s*z**2 - 2*d**3*m*p**2*s*w + 4*d**3*m*p*s*v*z - 4*d**3*m*p*s*w*z + 4*d**3*m*s*v*z**2 - 2*d**3*m*s*w*z**2 - 2*d**3*m*s*y*z**2 + 2*d**3*n*p**2*s*w - 4*d**3*n*p*s*v*z + 4*d**3*n*p*s*w*z - 4*d**3*n*s*v*z**2 + 2*d**3*n*s*w*z**2 + 2*d**3*n*s*y*z**2 - 2*d**3*p**2*q*s*x + 2*d**3*p**2*r*s*x - 4*d**3*p*q*s*x*z + 4*d**3*p*r*s*x*z - 2*d**3*q*s*u*z**2 - 2*d**3*q*s*x*z**2 + 2*d**3*r*s*u*z**2 + 2*d**3*r*s*x*z**2 - d**2*f*g*p**2*s**2 - 2*d**2*f*k*p*s**2*z - 2*d**2*f*k*s**2*z**2 + d**2*f*p**2*s**2*x + 2*d**2*f*p*s**2*x*z + d**2*f*s**2*u*z**2 + d**2*f*s**2*x*z**2 + 6*d**2*g*p**2*q*s**2 - 6*d**2*g*p**2*r*s**2 + d**2*g*p**2*s**2*w - 2*d**2*g*p*s**2*v*z + 2*d**2*g*p*s**2*w*z - 2*d**2*g*s**2*v*z**2 + d**2*g*s**2*w*z**2 + d**2*g*s**2*y*z**2 - 4*d**2*h*p**2*q*s**2 + 6*d**2*h*p**2*r*s**2 - 2*d**2*h*p**2*s**2*w + 4*d**2*h*p*s**2*v*z - 4*d**2*h*p*s**2*w*z + 4*d**2*h*s**2*v*z**2 - 2*d**2*h*s**2*w*z**2 - 2*d**2*h*s**2*y*z**2 + 4*d**2*k*p*q*s**2*z - 2*d**2*k*p*r*s**2*z + 4*d**2*k*q*s**2*z**2 - 2*d**2*k*r*s**2*z**2 - d**2*l*p**2*r*s**2 + d**2*l*p**2*s**2*w - 2*d**2*l*p*s**2*v*z + 2*d**2*l*p*s**2*w*z - 2*d**2*l*s**2*v*z**2 + d**2*l*s**2*w*z**2 + d**2*l*s**2*y*z**2 - d**2*m*p**2*s**2*w + 2*d**2*m*p*s**2*v*z - 2*d**2*m*p*s**2*w*z + 2*d**2*m*s**2*v*z**2 - d**2*m*s**2*w*z**2 - d**2*m*s**2*y*z**2 + 2*d**2*n*p**2*s**2*w - 4*d**2*n*p*s**2*v*z + 4*d**2*n*p*s**2*w*z - 4*d**2*n*s**2*v*z**2 + 2*d**2*n*s**2*w*z**2 + 2*d**2*n*s**2*y*z**2 - d**2*o*p**2*s**2*w + 2*d**2*o*p*s**2*v*z - 2*d**2*o*p*s**2*w*z + 2*d**2*o*s**2*v*z**2 - d**2*o*s**2*w*z**2 - d**2*o*s**2*y*z**2 - 2*d**2*p**2*q*s**2*x + d**2*p**2*r*s**2*x - 4*d**2*p*q*s**2*x*z + 2*d**2*p*r*s**2*x*z - 2*d**2*q*s**2*u*z**2 - 2*d**2*q*s**2*x*z**2 + d**2*r*s**2*u*z**2 + d**2*r*s**2*x*z**2 - 2*d*f*g*p**2*s**3 + 2*d*f*h*p**2*s**3 + 6*d*g*p**2*q*s**3 - 4*d*g*p**2*r*s**3 - 8*d*h*p**2*q*s**3 + 6*d*h*p**2*r*s**3 + 2*d*l*p**2*q*s**3 - 2*d*l*p**2*r*s**3 - f*g*p**2*s**4 + 2*f*h*p**2*s**4 - f*l*p**2*s**4 + 2*g*p**2*q*s**4 - g*p**2*r*s**4 - 4*h*p**2*q*s**4 + 2*h*p**2*r*s**4 + 2*l*p**2*q*s**4 - l*p**2*r*s**4) / (d**4*p**2)
    a1 = (-2*a*d**4*k*p - 4*a*d**4*k*z + 2*a*d**4*p*x + 2*a*d**4*u*z + 2*a*d**4*x*z - 4*a*d**3*k*p*s - 4*a*d**3*k*p*z - 8*a*d**3*k*s*z - 4*a*d**3*k*z**2 - 4*a*d**3*m*p**2 + 2*a*d**3*n*p**2 + 2*a*d**3*p**2*x + 4*a*d**3*p*s*x + 4*a*d**3*p*x*z + 4*a*d**3*s*u*z + 4*a*d**3*s*x*z + 2*a*d**3*u*z**2 + 2*a*d**3*x*z**2 - 2*a*d**2*k*p*s**2 - 4*a*d**2*k*p*s*z - 4*a*d**2*k*s**2*z - 4*a*d**2*k*s*z**2 - 12*a*d**2*m*p**2*s + 12*a*d**2*n*p**2*s - 2*a*d**2*o*p**2*s + 2*a*d**2*p**2*s*x + 2*a*d**2*p*s**2*x + 4*a*d**2*p*s*x*z + 2*a*d**2*s**2*u*z + 2*a*d**2*s**2*x*z + 2*a*d**2*s*u*z**2 + 2*a*d**2*s*x*z**2 - 12*a*d*m*p**2*s**2 + 18*a*d*n*p**2*s**2 - 6*a*d*o*p**2*s**2 - 4*a*m*p**2*s**3 + 8*a*n*p**2*s**3 - 4*a*o*p**2*s**3 + 4*b*d**3*k*p*s + 4*b*d**3*k*p*z + 8*b*d**3*k*s*z + 4*b*d**3*k*z**2 + 2*b*d**3*m*p**2 - 2*b*d**3*p**2*x - 4*b*d**3*p*s*x - 4*b*d**3*p*x*z - 4*b*d**3*s*u*z - 4*b*d**3*s*x*z - 2*b*d**3*u*z**2 - 2*b*d**3*x*z**2 + 4*b*d**2*k*p*s**2 + 8*b*d**2*k*p*s*z + 8*b*d**2*k*s**2*z + 8*b*d**2*k*s*z**2 + 12*b*d**2*m*p**2*s - 8*b*d**2*n*p**2*s - 4*b*d**2*p**2*s*x - 4*b*d**2*p*s**2*x - 8*b*d**2*p*s*x*z - 4*b*d**2*s**2*u*z - 4*b*d**2*s**2*x*z - 4*b*d**2*s*u*z**2 - 4*b*d**2*s*x*z**2 + 18*b*d*m*p**2*s**2 - 24*b*d*n*p**2*s**2 + 6*b*d*o*p**2*s**2 + 8*b*m*p**2*s**3 - 16*b*n*p**2*s**3 + 8*b*o*p**2*s**3 - 2*c*d**2*k*p*s**2 - 4*c*d**2*k*p*s*z - 4*c*d**2*k*s**2*z - 4*c*d**2*k*s*z**2 - 2*c*d**2*m*p**2*s + 2*c*d**2*p**2*s*x + 2*c*d**2*p*s**2*x + 4*c*d**2*p*s*x*z + 2*c*d**2*s**2*u*z + 2*c*d**2*s**2*x*z + 2*c*d**2*s*u*z**2 + 2*c*d**2*s*x*z**2 - 6*c*d*m*p**2*s**2 + 6*c*d*n*p**2*s**2 - 4*c*m*p**2*s**3 + 8*c*n*p**2*s**3 - 4*c*o*p**2*s**3 + 2*d**4*g*p*v - 2*d**4*g*p*w + 4*d**4*g*v*z - 2*d**4*g*w*z - 2*d**4*g*y*z + 2*d**4*k*p*r + 4*d**4*k*r*z - 2*d**4*m*p*v + 2*d**4*m*p*w - 4*d**4*m*v*z + 2*d**4*m*w*z + 2*d**4*m*y*z - 2*d**4*p*r*x - 2*d**4*r*u*z - 2*d**4*r*x*z - 2*d**3*g*p**2*q + 4*d**3*g*p**2*r - 2*d**3*g*p**2*w + 4*d**3*g*p*s*v - 4*d**3*g*p*s*w + 4*d**3*g*p*v*z - 4*d**3*g*p*w*z + 8*d**3*g*s*v*z - 4*d**3*g*s*w*z - 4*d**3*g*s*y*z + 4*d**3*g*v*z**2 - 2*d**3*g*w*z**2 - 2*d**3*g*y*z**2 - 2*d**3*h*p**2*r + 2*d**3*h*p**2*w - 4*d**3*h*p*s*v + 4*d**3*h*p*s*w - 4*d**3*h*p*v*z + 4*d**3*h*p*w*z - 8*d**3*h*s*v*z + 4*d**3*h*s*w*z + 4*d**3*h*s*y*z - 4*d**3*h*v*z**2 + 2*d**3*h*w*z**2 + 2*d**3*h*y*z**2 - 4*d**3*k*p*q*s - 4*d**3*k*p*q*z + 4*d**3*k*p*r*s + 4*d**3*k*p*r*z - 8*d**3*k*q*s*z - 4*d**3*k*q*z**2 + 8*d**3*k*r*s*z + 4*d**3*k*r*z**2 + 2*d**3*m*p**2*w - 4*d**3*m*p*s*v + 4*d**3*m*p*s*w - 4*d**3*m*p*v*z + 4*d**3*m*p*w*z - 8*d**3*m*s*v*z + 4*d**3*m*s*w*z + 4*d**3*m*s*y*z - 4*d**3*m*v*z**2 + 2*d**3*m*w*z**2 + 2*d**3*m*y*z**2 - 2*d**3*n*p**2*w + 4*d**3*n*p*s*v - 4*d**3*n*p*s*w + 4*d**3*n*p*v*z - 4*d**3*n*p*w*z + 8*d**3*n*s*v*z - 4*d**3*n*s*w*z - 4*d**3*n*s*y*z + 4*d**3*n*v*z**2 - 2*d**3*n*w*z**2 - 2*d**3*n*y*z**2 + 2*d**3*p**2*q*x - 2*d**3*p**2*r*x + 4*d**3*p*q*s*x + 4*d**3*p*q*x*z - 4*d**3*p*r*s*x - 4*d**3*p*r*x*z + 4*d**3*q*s*u*z + 4*d**3*q*s*x*z + 2*d**3*q*u*z**2 + 2*d**3*q*x*z**2 - 4*d**3*r*s*u*z - 4*d**3*r*s*x*z - 2*d**3*r*u*z**2 - 2*d**3*r*x*z**2 + 2*d**2*f*g*p**2*s + 2*d**2*f*k*p*s**2 + 4*d**2*f*k*p*s*z + 4*d**2*f*k*s**2*z + 4*d**2*f*k*s*z**2 - 2*d**2*f*p**2*s*x - 2*d**2*f*p*s**2*x - 4*d**2*f*p*s*x*z - 2*d**2*f*s**2*u*z - 2*d**2*f*s**2*x*z - 2*d**2*f*s*u*z**2 - 2*d**2*f*s*x*z**2 - 12*d**2*g*p**2*q*s + 12*d**2*g*p**2*r*s - 2*d**2*g*p**2*s*w + 2*d**2*g*p*s**2*v - 2*d**2*g*p*s**2*w + 4*d**2*g*p*s*v*z - 4*d**2*g*p*s*w*z + 4*d**2*g*s**2*v*z - 2*d**2*g*s**2*w*z - 2*d**2*g*s**2*y*z + 4*d**2*g*s*v*z**2 - 2*d**2*g*s*w*z**2 - 2*d**2*g*s*y*z**2 + 8*d**2*h*p**2*q*s - 12*d**2*h*p**2*r*s + 4*d**2*h*p**2*s*w - 4*d**2*h*p*s**2*v + 4*d**2*h*p*s**2*w - 8*d**2*h*p*s*v*z + 8*d**2*h*p*s*w*z - 8*d**2*h*s**2*v*z + 4*d**2*h*s**2*w*z + 4*d**2*h*s**2*y*z - 8*d**2*h*s*v*z**2 + 4*d**2*h*s*w*z**2 + 4*d**2*h*s*y*z**2 - 4*d**2*k*p*q*s**2 - 8*d**2*k*p*q*s*z + 2*d**2*k*p*r*s**2 + 4*d**2*k*p*r*s*z - 8*d**2*k*q*s**2*z - 8*d**2*k*q*s*z**2 + 4*d**2*k*r*s**2*z + 4*d**2*k*r*s*z**2 + 2*d**2*l*p**2*r*s - 2*d**2*l*p**2*s*w + 2*d**2*l*p*s**2*v - 2*d**2*l*p*s**2*w + 4*d**2*l*p*s*v*z - 4*d**2*l*p*s*w*z + 4*d**2*l*s**2*v*z - 2*d**2*l*s**2*w*z - 2*d**2*l*s**2*y*z + 4*d**2*l*s*v*z**2 - 2*d**2*l*s*w*z**2 - 2*d**2*l*s*y*z**2 + 2*d**2*m*p**2*s*w - 2*d**2*m*p*s**2*v + 2*d**2*m*p*s**2*w - 4*d**2*m*p*s*v*z + 4*d**2*m*p*s*w*z - 4*d**2*m*s**2*v*z + 2*d**2*m*s**2*w*z + 2*d**2*m*s**2*y*z - 4*d**2*m*s*v*z**2 + 2*d**2*m*s*w*z**2 + 2*d**2*m*s*y*z**2 - 4*d**2*n*p**2*s*w + 4*d**2*n*p*s**2*v - 4*d**2*n*p*s**2*w + 8*d**2*n*p*s*v*z - 8*d**2*n*p*s*w*z + 8*d**2*n*s**2*v*z - 4*d**2*n*s**2*w*z - 4*d**2*n*s**2*y*z + 8*d**2*n*s*v*z**2 - 4*d**2*n*s*w*z**2 - 4*d**2*n*s*y*z**2 + 2*d**2*o*p**2*s*w - 2*d**2*o*p*s**2*v + 2*d**2*o*p*s**2*w - 4*d**2*o*p*s*v*z + 4*d**2*o*p*s*w*z - 4*d**2*o*s**2*v*z + 2*d**2*o*s**2*w*z + 2*d**2*o*s**2*y*z - 4*d**2*o*s*v*z**2 + 2*d**2*o*s*w*z**2 + 2*d**2*o*s*y*z**2 + 4*d**2*p**2*q*s*x - 2*d**2*p**2*r*s*x + 4*d**2*p*q*s**2*x + 8*d**2*p*q*s*x*z - 2*d**2*p*r*s**2*x - 4*d**2*p*r*s*x*z + 4*d**2*q*s**2*u*z + 4*d**2*q*s**2*x*z + 4*d**2*q*s*u*z**2 + 4*d**2*q*s*x*z**2 - 2*d**2*r*s**2*u*z - 2*d**2*r*s**2*x*z - 2*d**2*r*s*u*z**2 - 2*d**2*r*s*x*z**2 + 6*d*f*g*p**2*s**2 - 6*d*f*h*p**2*s**2 - 18*d*g*p**2*q*s**2 + 12*d*g*p**2*r*s**2 + 24*d*h*p**2*q*s**2 - 18*d*h*p**2*r*s**2 - 6*d*l*p**2*q*s**2 + 6*d*l*p**2*r*s**2 + 4*f*g*p**2*s**3 - 8*f*h*p**2*s**3 + 4*f*l*p**2*s**3 - 8*g*p**2*q*s**3 + 4*g*p**2*r*s**3 + 16*h*p**2*q*s**3 - 8*h*p**2*r*s**3 - 8*l*p**2*q*s**3 + 4*l*p**2*r*s**3) / (d**4*p**2)
    a2 = (+2*a*d**4*k - a*d**4*u - a*d**4*x + 4*a*d**3*k*p + 4*a*d**3*k*s + 8*a*d**3*k*z - 4*a*d**3*p*x - 2*a*d**3*s*u - 2*a*d**3*s*x - 4*a*d**3*u*z - 4*a*d**3*x*z + 4*a*d**2*k*p*s + 2*a*d**2*k*p*z + 2*a*d**2*k*s**2 + 8*a*d**2*k*s*z + 2*a*d**2*k*z**2 + 6*a*d**2*m*p**2 - 6*a*d**2*n*p**2 + a*d**2*o*p**2 - a*d**2*p**2*x - 4*a*d**2*p*s*x - 2*a*d**2*p*x*z - a*d**2*s**2*u - a*d**2*s**2*x - 4*a*d**2*s*u*z - 4*a*d**2*s*x*z - a*d**2*u*z**2 - a*d**2*x*z**2 + 12*a*d*m*p**2*s - 18*a*d*n*p**2*s + 6*a*d*o*p**2*s + 6*a*m*p**2*s**2 - 12*a*n*p**2*s**2 + 6*a*o*p**2*s**2 - 4*b*d**3*k*p - 4*b*d**3*k*s - 8*b*d**3*k*z + 4*b*d**3*p*x + 2*b*d**3*s*u + 2*b*d**3*s*x + 4*b*d**3*u*z + 4*b*d**3*x*z - 8*b*d**2*k*p*s - 4*b*d**2*k*p*z - 4*b*d**2*k*s**2 - 16*b*d**2*k*s*z - 4*b*d**2*k*z**2 - 6*b*d**2*m*p**2 + 4*b*d**2*n*p**2 + 2*b*d**2*p**2*x + 8*b*d**2*p*s*x + 4*b*d**2*p*x*z + 2*b*d**2*s**2*u + 2*b*d**2*s**2*x + 8*b*d**2*s*u*z + 8*b*d**2*s*x*z + 2*b*d**2*u*z**2 + 2*b*d**2*x*z**2 - 18*b*d*m*p**2*s + 24*b*d*n*p**2*s - 6*b*d*o*p**2*s - 12*b*m*p**2*s**2 + 24*b*n*p**2*s**2 - 12*b*o*p**2*s**2 + 4*c*d**2*k*p*s + 2*c*d**2*k*p*z + 2*c*d**2*k*s**2 + 8*c*d**2*k*s*z + 2*c*d**2*k*z**2 + c*d**2*m*p**2 - c*d**2*p**2*x - 4*c*d**2*p*s*x - 2*c*d**2*p*x*z - c*d**2*s**2*u - c*d**2*s**2*x - 4*c*d**2*s*u*z - 4*c*d**2*s*x*z - c*d**2*u*z**2 - c*d**2*x*z**2 + 6*c*d*m*p**2*s - 6*c*d*n*p**2*s + 6*c*m*p**2*s**2 - 12*c*n*p**2*s**2 + 6*c*o*p**2*s**2 - 2*d**4*g*v + d**4*g*w + d**4*g*y - 2*d**4*k*r + 2*d**4*m*v - d**4*m*w - d**4*m*y + d**4*r*u + d**4*r*x - 4*d**3*g*p*v + 4*d**3*g*p*w - 4*d**3*g*s*v + 2*d**3*g*s*w + 2*d**3*g*s*y - 8*d**3*g*v*z + 4*d**3*g*w*z + 4*d**3*g*y*z + 4*d**3*h*p*v - 4*d**3*h*p*w + 4*d**3*h*s*v - 2*d**3*h*s*w - 2*d**3*h*s*y + 8*d**3*h*v*z - 4*d**3*h*w*z - 4*d**3*h*y*z + 4*d**3*k*p*q - 4*d**3*k*p*r + 4*d**3*k*q*s + 8*d**3*k*q*z - 4*d**3*k*r*s - 8*d**3*k*r*z + 4*d**3*m*p*v - 4*d**3*m*p*w + 4*d**3*m*s*v - 2*d**3*m*s*w - 2*d**3*m*s*y + 8*d**3*m*v*z - 4*d**3*m*w*z - 4*d**3*m*y*z - 4*d**3*n*p*v + 4*d**3*n*p*w - 4*d**3*n*s*v + 2*d**3*n*s*w + 2*d**3*n*s*y - 8*d**3*n*v*z + 4*d**3*n*w*z + 4*d**3*n*y*z - 4*d**3*p*q*x + 4*d**3*p*r*x - 2*d**3*q*s*u - 2*d**3*q*s*x - 4*d**3*q*u*z - 4*d**3*q*x*z + 2*d**3*r*s*u + 2*d**3*r*s*x + 4*d**3*r*u*z + 4*d**3*r*x*z - d**2*f*g*p**2 - 4*d**2*f*k*p*s - 2*d**2*f*k*p*z - 2*d**2*f*k*s**2 - 8*d**2*f*k*s*z - 2*d**2*f*k*z**2 + d**2*f*p**2*x + 4*d**2*f*p*s*x + 2*d**2*f*p*x*z + d**2*f*s**2*u + d**2*f*s**2*x + 4*d**2*f*s*u*z + 4*d**2*f*s*x*z + d**2*f*u*z**2 + d**2*f*x*z**2 + 6*d**2*g*p**2*q - 6*d**2*g*p**2*r + d**2*g*p**2*w - 4*d**2*g*p*s*v + 4*d**2*g*p*s*w - 2*d**2*g*p*v*z + 2*d**2*g*p*w*z - 2*d**2*g*s**2*v + d**2*g*s**2*w + d**2*g*s**2*y - 8*d**2*g*s*v*z + 4*d**2*g*s*w*z + 4*d**2*g*s*y*z - 2*d**2*g*v*z**2 + d**2*g*w*z**2 + d**2*g*y*z**2 - 4*d**2*h*p**2*q + 6*d**2*h*p**2*r - 2*d**2*h*p**2*w + 8*d**2*h*p*s*v - 8*d**2*h*p*s*w + 4*d**2*h*p*v*z - 4*d**2*h*p*w*z + 4*d**2*h*s**2*v - 2*d**2*h*s**2*w - 2*d**2*h*s**2*y + 16*d**2*h*s*v*z - 8*d**2*h*s*w*z - 8*d**2*h*s*y*z + 4*d**2*h*v*z**2 - 2*d**2*h*w*z**2 - 2*d**2*h*y*z**2 + 8*d**2*k*p*q*s + 4*d**2*k*p*q*z - 4*d**2*k*p*r*s - 2*d**2*k*p*r*z + 4*d**2*k*q*s**2 + 16*d**2*k*q*s*z + 4*d**2*k*q*z**2 - 2*d**2*k*r*s**2 - 8*d**2*k*r*s*z - 2*d**2*k*r*z**2 - d**2*l*p**2*r + d**2*l*p**2*w - 4*d**2*l*p*s*v + 4*d**2*l*p*s*w - 2*d**2*l*p*v*z + 2*d**2*l*p*w*z - 2*d**2*l*s**2*v + d**2*l*s**2*w + d**2*l*s**2*y - 8*d**2*l*s*v*z + 4*d**2*l*s*w*z + 4*d**2*l*s*y*z - 2*d**2*l*v*z**2 + d**2*l*w*z**2 + d**2*l*y*z**2 - d**2*m*p**2*w + 4*d**2*m*p*s*v - 4*d**2*m*p*s*w + 2*d**2*m*p*v*z - 2*d**2*m*p*w*z + 2*d**2*m*s**2*v - d**2*m*s**2*w - d**2*m*s**2*y + 8*d**2*m*s*v*z - 4*d**2*m*s*w*z - 4*d**2*m*s*y*z + 2*d**2*m*v*z**2 - d**2*m*w*z**2 - d**2*m*y*z**2 + 2*d**2*n*p**2*w - 8*d**2*n*p*s*v + 8*d**2*n*p*s*w - 4*d**2*n*p*v*z + 4*d**2*n*p*w*z - 4*d**2*n*s**2*v + 2*d**2*n*s**2*w + 2*d**2*n*s**2*y - 16*d**2*n*s*v*z + 8*d**2*n*s*w*z + 8*d**2*n*s*y*z - 4*d**2*n*v*z**2 + 2*d**2*n*w*z**2 + 2*d**2*n*y*z**2 - d**2*o*p**2*w + 4*d**2*o*p*s*v - 4*d**2*o*p*s*w + 2*d**2*o*p*v*z - 2*d**2*o*p*w*z + 2*d**2*o*s**2*v - d**2*o*s**2*w - d**2*o*s**2*y + 8*d**2*o*s*v*z - 4*d**2*o*s*w*z - 4*d**2*o*s*y*z + 2*d**2*o*v*z**2 - d**2*o*w*z**2 - d**2*o*y*z**2 - 2*d**2*p**2*q*x + d**2*p**2*r*x - 8*d**2*p*q*s*x - 4*d**2*p*q*x*z + 4*d**2*p*r*s*x + 2*d**2*p*r*x*z - 2*d**2*q*s**2*u - 2*d**2*q*s**2*x - 8*d**2*q*s*u*z - 8*d**2*q*s*x*z - 2*d**2*q*u*z**2 - 2*d**2*q*x*z**2 + d**2*r*s**2*u + d**2*r*s**2*x + 4*d**2*r*s*u*z + 4*d**2*r*s*x*z + d**2*r*u*z**2 + d**2*r*x*z**2 - 6*d*f*g*p**2*s + 6*d*f*h*p**2*s + 18*d*g*p**2*q*s - 12*d*g*p**2*r*s - 24*d*h*p**2*q*s + 18*d*h*p**2*r*s + 6*d*l*p**2*q*s - 6*d*l*p**2*r*s - 6*f*g*p**2*s**2 + 12*f*h*p**2*s**2 - 6*f*l*p**2*s**2 + 12*g*p**2*q*s**2 - 6*g*p**2*r*s**2 - 24*h*p**2*q*s**2 + 12*h*p**2*r*s**2 + 12*l*p**2*q*s**2 - 6*l*p**2*r*s**2) / (d**4*p**2)
    a3 = (-4*a*d**3*k + 2*a*d**3*u + 2*a*d**3*x - 2*a*d**2*k*p - 4*a*d**2*k*s - 4*a*d**2*k*z + 2*a*d**2*p*x + 2*a*d**2*s*u + 2*a*d**2*s*x + 2*a*d**2*u*z + 2*a*d**2*x*z - 4*a*d*m*p**2 + 6*a*d*n*p**2 - 2*a*d*o*p**2 - 4*a*m*p**2*s + 8*a*n*p**2*s - 4*a*o*p**2*s + 4*b*d**3*k - 2*b*d**3*u - 2*b*d**3*x + 4*b*d**2*k*p + 8*b*d**2*k*s + 8*b*d**2*k*z - 4*b*d**2*p*x - 4*b*d**2*s*u - 4*b*d**2*s*x - 4*b*d**2*u*z - 4*b*d**2*x*z + 6*b*d*m*p**2 - 8*b*d*n*p**2 + 2*b*d*o*p**2 + 8*b*m*p**2*s - 16*b*n*p**2*s + 8*b*o*p**2*s - 2*c*d**2*k*p - 4*c*d**2*k*s - 4*c*d**2*k*z + 2*c*d**2*p*x + 2*c*d**2*s*u + 2*c*d**2*s*x + 2*c*d**2*u*z + 2*c*d**2*x*z - 2*c*d*m*p**2 + 2*c*d*n*p**2 - 4*c*m*p**2*s + 8*c*n*p**2*s - 4*c*o*p**2*s + 4*d**3*g*v - 2*d**3*g*w - 2*d**3*g*y - 4*d**3*h*v + 2*d**3*h*w + 2*d**3*h*y - 4*d**3*k*q + 4*d**3*k*r - 4*d**3*m*v + 2*d**3*m*w + 2*d**3*m*y + 4*d**3*n*v - 2*d**3*n*w - 2*d**3*n*y + 2*d**3*q*u + 2*d**3*q*x - 2*d**3*r*u - 2*d**3*r*x + 2*d**2*f*k*p + 4*d**2*f*k*s + 4*d**2*f*k*z - 2*d**2*f*p*x - 2*d**2*f*s*u - 2*d**2*f*s*x - 2*d**2*f*u*z - 2*d**2*f*x*z + 2*d**2*g*p*v - 2*d**2*g*p*w + 4*d**2*g*s*v - 2*d**2*g*s*w - 2*d**2*g*s*y + 4*d**2*g*v*z - 2*d**2*g*w*z - 2*d**2*g*y*z - 4*d**2*h*p*v + 4*d**2*h*p*w - 8*d**2*h*s*v + 4*d**2*h*s*w + 4*d**2*h*s*y - 8*d**2*h*v*z + 4*d**2*h*w*z + 4*d**2*h*y*z - 4*d**2*k*p*q + 2*d**2*k*p*r - 8*d**2*k*q*s - 8*d**2*k*q*z + 4*d**2*k*r*s + 4*d**2*k*r*z + 2*d**2*l*p*v - 2*d**2*l*p*w + 4*d**2*l*s*v - 2*d**2*l*s*w - 2*d**2*l*s*y + 4*d**2*l*v*z - 2*d**2*l*w*z - 2*d**2*l*y*z - 2*d**2*m*p*v + 2*d**2*m*p*w - 4*d**2*m*s*v + 2*d**2*m*s*w + 2*d**2*m*s*y - 4*d**2*m*v*z + 2*d**2*m*w*z + 2*d**2*m*y*z + 4*d**2*n*p*v - 4*d**2*n*p*w + 8*d**2*n*s*v - 4*d**2*n*s*w - 4*d**2*n*s*y + 8*d**2*n*v*z - 4*d**2*n*w*z - 4*d**2*n*y*z - 2*d**2*o*p*v + 2*d**2*o*p*w - 4*d**2*o*s*v + 2*d**2*o*s*w + 2*d**2*o*s*y - 4*d**2*o*v*z + 2*d**2*o*w*z + 2*d**2*o*y*z + 4*d**2*p*q*x - 2*d**2*p*r*x + 4*d**2*q*s*u + 4*d**2*q*s*x + 4*d**2*q*u*z + 4*d**2*q*x*z - 2*d**2*r*s*u - 2*d**2*r*s*x - 2*d**2*r*u*z - 2*d**2*r*x*z + 2*d*f*g*p**2 - 2*d*f*h*p**2 - 6*d*g*p**2*q + 4*d*g*p**2*r + 8*d*h*p**2*q - 6*d*h*p**2*r - 2*d*l*p**2*q + 2*d*l*p**2*r + 4*f*g*p**2*s - 8*f*h*p**2*s + 4*f*l*p**2*s - 8*g*p**2*q*s + 4*g*p**2*r*s + 16*h*p**2*q*s - 8*h*p**2*r*s - 8*l*p**2*q*s + 4*l*p**2*r*s) / (d**4*p**2)
    a4 = (+2*a*d**2*k - a*d**2*u - a*d**2*x + a*m*p**2 - 2*a*n*p**2 + a*o*p**2 - 4*b*d**2*k + 2*b*d**2*u + 2*b*d**2*x - 2*b*m*p**2 + 4*b*n*p**2 - 2*b*o*p**2 + 2*c*d**2*k - c*d**2*u - c*d**2*x + c*m*p**2 - 2*c*n*p**2 + c*o*p**2 - 2*d**2*f*k + d**2*f*u + d**2*f*x - 2*d**2*g*v + d**2*g*w + d**2*g*y + 4*d**2*h*v - 2*d**2*h*w - 2*d**2*h*y + 4*d**2*k*q - 2*d**2*k*r - 2*d**2*l*v + d**2*l*w + d**2*l*y + 2*d**2*m*v - d**2*m*w - d**2*m*y - 4*d**2*n*v + 2*d**2*n*w + 2*d**2*n*y + 2*d**2*o*v - d**2*o*w - d**2*o*y - 2*d**2*q*u - 2*d**2*q*x + d**2*r*u + d**2*r*x - f*g*p**2 + 2*f*h*p**2 - f*l*p**2 + 2*g*p**2*q - g*p**2*r - 4*h*p**2*q + 2*h*p**2*r + 2*l*p**2*q - l*p**2*r) / (d**4*p**2)
    """

    """
    a0 = (+2*a*d**4*kk*p*z + 2*a*d**4*kk*z**2 + a*d**4*m*p**2 - a*d**4*p**2*xx - 2*a*d**4*p*xx*z - a*d**4*uu*z**2 - a*d**4*xx*z**2 + 4*a*d**3*kk*p*s*z + 4*a*d**3*kk*s*z**2 + 4*a*d**3*m*p**2*s - 2*a*d**3*n*p**2*s - 2*a*d**3*p**2*s*xx - 4*a*d**3*p*s*xx*z - 2*a*d**3*s*uu*z**2 - 2*a*d**3*s*xx*z**2 + 2*a*d**2*kk*p*s**2*z + 2*a*d**2*kk*s**2*z**2 + 6*a*d**2*m*p**2*s**2 - 6*a*d**2*n*p**2*s**2 + a*d**2*o*p**2*s**2 - a*d**2*p**2*s**2*xx - 2*a*d**2*p*s**2*xx*z - a*d**2*s**2*uu*z**2 - a*d**2*s**2*xx*z**2 + 4*a*d*m*p**2*s**3 - 6*a*d*n*p**2*s**3 + 2*a*d*o*p**2*s**3 + a*m*p**2*s**4 - 2*a*n*p**2*s**4 + a*o*p**2*s**4 - 4*b*d**3*kk*p*s*z - 4*b*d**3*kk*s*z**2 - 2*b*d**3*m*p**2*s + 2*b*d**3*p**2*s*xx + 4*b*d**3*p*s*xx*z + 2*b*d**3*s*uu*z**2 + 2*b*d**3*s*xx*z**2 - 4*b*d**2*kk*p*s**2*z - 4*b*d**2*kk*s**2*z**2 - 6*b*d**2*m*p**2*s**2 + 4*b*d**2*n*p**2*s**2 + 2*b*d**2*p**2*s**2*xx + 4*b*d**2*p*s**2*xx*z + 2*b*d**2*s**2*uu*z**2 + 2*b*d**2*s**2*xx*z**2 - 6*b*d*m*p**2*s**3 + 8*b*d*n*p**2*s**3 - 2*b*d*o*p**2*s**3 - 2*b*m*p**2*s**4 + 4*b*n*p**2*s**4 - 2*b*o*p**2*s**4 + 2*c*d**2*kk*p*s**2*z + 2*c*d**2*kk*s**2*z**2 + c*d**2*m*p**2*s**2 - c*d**2*p**2*s**2*xx - 2*c*d**2*p*s**2*xx*z - c*d**2*s**2*uu*z**2 - c*d**2*s**2*xx*z**2 + 2*c*d*m*p**2*s**3 - 2*c*d*n*p**2*s**3 + c*m*p**2*s**4 - 2*c*n*p**2*s**4 + c*o*p**2*s**4 - d**4*g*p**2*r + d**4*g*p**2*ww - 2*d**4*g*p*vv*z + 2*d**4*g*p*ww*z - 2*d**4*g*vv*z**2 + d**4*g*ww*z**2 + d**4*g*yy*z**2 - 2*d**4*kk*p*r*z - 2*d**4*kk*r*z**2 - d**4*m*p**2*ww + 2*d**4*m*p*vv*z - 2*d**4*m*p*ww*z + 2*d**4*m*vv*z**2 - d**4*m*ww*z**2 - d**4*m*yy*z**2 + d**4*p**2*r*xx + 2*d**4*p*r*xx*z + d**4*r*uu*z**2 + d**4*r*xx*z**2 + 2*d**3*g*p**2*q*s - 4*d**3*g*p**2*r*s + 2*d**3*g*p**2*s*ww - 4*d**3*g*p*s*vv*z + 4*d**3*g*p*s*ww*z - 4*d**3*g*s*vv*z**2 + 2*d**3*g*s*ww*z**2 + 2*d**3*g*s*yy*z**2 + 2*d**3*h*p**2*r*s - 2*d**3*h*p**2*s*ww + 4*d**3*h*p*s*vv*z - 4*d**3*h*p*s*ww*z + 4*d**3*h*s*vv*z**2 - 2*d**3*h*s*ww*z**2 - 2*d**3*h*s*yy*z**2 + 4*d**3*kk*p*q*s*z - 4*d**3*kk*p*r*s*z + 4*d**3*kk*q*s*z**2 - 4*d**3*kk*r*s*z**2 - 2*d**3*m*p**2*s*ww + 4*d**3*m*p*s*vv*z - 4*d**3*m*p*s*ww*z + 4*d**3*m*s*vv*z**2 - 2*d**3*m*s*ww*z**2 - 2*d**3*m*s*yy*z**2 + 2*d**3*n*p**2*s*ww - 4*d**3*n*p*s*vv*z + 4*d**3*n*p*s*ww*z - 4*d**3*n*s*vv*z**2 + 2*d**3*n*s*ww*z**2 + 2*d**3*n*s*yy*z**2 - 2*d**3*p**2*q*s*xx + 2*d**3*p**2*r*s*xx - 4*d**3*p*q*s*xx*z + 4*d**3*p*r*s*xx*z - 2*d**3*q*s*uu*z**2 - 2*d**3*q*s*xx*z**2 + 2*d**3*r*s*uu*z**2 + 2*d**3*r*s*xx*z**2 - d**2*f*g*p**2*s**2 - 2*d**2*f*kk*p*s**2*z - 2*d**2*f*kk*s**2*z**2 + d**2*f*p**2*s**2*xx + 2*d**2*f*p*s**2*xx*z + d**2*f*s**2*uu*z**2 + d**2*f*s**2*xx*z**2 + 6*d**2*g*p**2*q*s**2 - 6*d**2*g*p**2*r*s**2 + d**2*g*p**2*s**2*ww - 2*d**2*g*p*s**2*vv*z + 2*d**2*g*p*s**2*ww*z - 2*d**2*g*s**2*vv*z**2 + d**2*g*s**2*ww*z**2 + d**2*g*s**2*yy*z**2 - 4*d**2*h*p**2*q*s**2 + 6*d**2*h*p**2*r*s**2 - 2*d**2*h*p**2*s**2*ww + 4*d**2*h*p*s**2*vv*z - 4*d**2*h*p*s**2*ww*z + 4*d**2*h*s**2*vv*z**2 - 2*d**2*h*s**2*ww*z**2 - 2*d**2*h*s**2*yy*z**2 + 4*d**2*kk*p*q*s**2*z - 2*d**2*kk*p*r*s**2*z + 4*d**2*kk*q*s**2*z**2 - 2*d**2*kk*r*s**2*z**2 - d**2*l*p**2*r*s**2 + d**2*l*p**2*s**2*ww - 2*d**2*l*p*s**2*vv*z + 2*d**2*l*p*s**2*ww*z - 2*d**2*l*s**2*vv*z**2 + d**2*l*s**2*ww*z**2 + d**2*l*s**2*yy*z**2 - d**2*m*p**2*s**2*ww + 2*d**2*m*p*s**2*vv*z - 2*d**2*m*p*s**2*ww*z + 2*d**2*m*s**2*vv*z**2 - d**2*m*s**2*ww*z**2 - d**2*m*s**2*yy*z**2 + 2*d**2*n*p**2*s**2*ww - 4*d**2*n*p*s**2*vv*z + 4*d**2*n*p*s**2*ww*z - 4*d**2*n*s**2*vv*z**2 + 2*d**2*n*s**2*ww*z**2 + 2*d**2*n*s**2*yy*z**2 - d**2*o*p**2*s**2*ww + 2*d**2*o*p*s**2*vv*z - 2*d**2*o*p*s**2*ww*z + 2*d**2*o*s**2*vv*z**2 - d**2*o*s**2*ww*z**2 - d**2*o*s**2*yy*z**2 - 2*d**2*p**2*q*s**2*xx + d**2*p**2*r*s**2*xx - 4*d**2*p*q*s**2*xx*z + 2*d**2*p*r*s**2*xx*z - 2*d**2*q*s**2*uu*z**2 - 2*d**2*q*s**2*xx*z**2 + d**2*r*s**2*uu*z**2 + d**2*r*s**2*xx*z**2 - 2*d*f*g*p**2*s**3 + 2*d*f*h*p**2*s**3 + 6*d*g*p**2*q*s**3 - 4*d*g*p**2*r*s**3 - 8*d*h*p**2*q*s**3 + 6*d*h*p**2*r*s**3 + 2*d*l*p**2*q*s**3 - 2*d*l*p**2*r*s**3 - f*g*p**2*s**4 + 2*f*h*p**2*s**4 - f*l*p**2*s**4 + 2*g*p**2*q*s**4 - g*p**2*r*s**4 - 4*h*p**2*q*s**4 + 2*h*p**2*r*s**4 + 2*l*p**2*q*s**4 - l*p**2*r*s**4) / (d**4*p**2)
    a1 = (-2*a*d**4*kk*p - 4*a*d**4*kk*z + 2*a*d**4*p*xx + 2*a*d**4*uu*z + 2*a*d**4*xx*z - 4*a*d**3*kk*p*s - 4*a*d**3*kk*p*z - 8*a*d**3*kk*s*z - 4*a*d**3*kk*z**2 - 4*a*d**3*m*p**2 + 2*a*d**3*n*p**2 + 2*a*d**3*p**2*xx + 4*a*d**3*p*s*xx + 4*a*d**3*p*xx*z + 4*a*d**3*s*uu*z + 4*a*d**3*s*xx*z + 2*a*d**3*uu*z**2 + 2*a*d**3*xx*z**2 - 2*a*d**2*kk*p*s**2 - 4*a*d**2*kk*p*s*z - 4*a*d**2*kk*s**2*z - 4*a*d**2*kk*s*z**2 - 12*a*d**2*m*p**2*s + 12*a*d**2*n*p**2*s - 2*a*d**2*o*p**2*s + 2*a*d**2*p**2*s*xx + 2*a*d**2*p*s**2*xx + 4*a*d**2*p*s*xx*z + 2*a*d**2*s**2*uu*z + 2*a*d**2*s**2*xx*z + 2*a*d**2*s*uu*z**2 + 2*a*d**2*s*xx*z**2 - 12*a*d*m*p**2*s**2 + 18*a*d*n*p**2*s**2 - 6*a*d*o*p**2*s**2 - 4*a*m*p**2*s**3 + 8*a*n*p**2*s**3 - 4*a*o*p**2*s**3 + 4*b*d**3*kk*p*s + 4*b*d**3*kk*p*z + 8*b*d**3*kk*s*z + 4*b*d**3*kk*z**2 + 2*b*d**3*m*p**2 - 2*b*d**3*p**2*xx - 4*b*d**3*p*s*xx - 4*b*d**3*p*xx*z - 4*b*d**3*s*uu*z - 4*b*d**3*s*xx*z - 2*b*d**3*uu*z**2 - 2*b*d**3*xx*z**2 + 4*b*d**2*kk*p*s**2 + 8*b*d**2*kk*p*s*z + 8*b*d**2*kk*s**2*z + 8*b*d**2*kk*s*z**2 + 12*b*d**2*m*p**2*s - 8*b*d**2*n*p**2*s - 4*b*d**2*p**2*s*xx - 4*b*d**2*p*s**2*xx - 8*b*d**2*p*s*xx*z - 4*b*d**2*s**2*uu*z - 4*b*d**2*s**2*xx*z - 4*b*d**2*s*uu*z**2 - 4*b*d**2*s*xx*z**2 + 18*b*d*m*p**2*s**2 - 24*b*d*n*p**2*s**2 + 6*b*d*o*p**2*s**2 + 8*b*m*p**2*s**3 - 16*b*n*p**2*s**3 + 8*b*o*p**2*s**3 - 2*c*d**2*kk*p*s**2 - 4*c*d**2*kk*p*s*z - 4*c*d**2*kk*s**2*z - 4*c*d**2*kk*s*z**2 - 2*c*d**2*m*p**2*s + 2*c*d**2*p**2*s*xx + 2*c*d**2*p*s**2*xx + 4*c*d**2*p*s*xx*z + 2*c*d**2*s**2*uu*z + 2*c*d**2*s**2*xx*z + 2*c*d**2*s*uu*z**2 + 2*c*d**2*s*xx*z**2 - 6*c*d*m*p**2*s**2 + 6*c*d*n*p**2*s**2 - 4*c*m*p**2*s**3 + 8*c*n*p**2*s**3 - 4*c*o*p**2*s**3 + 2*d**4*g*p*vv - 2*d**4*g*p*ww + 4*d**4*g*vv*z - 2*d**4*g*ww*z - 2*d**4*g*yy*z + 2*d**4*kk*p*r + 4*d**4*kk*r*z - 2*d**4*m*p*vv + 2*d**4*m*p*ww - 4*d**4*m*vv*z + 2*d**4*m*ww*z + 2*d**4*m*yy*z - 2*d**4*p*r*xx - 2*d**4*r*uu*z - 2*d**4*r*xx*z - 2*d**3*g*p**2*q + 4*d**3*g*p**2*r - 2*d**3*g*p**2*ww + 4*d**3*g*p*s*vv - 4*d**3*g*p*s*ww + 4*d**3*g*p*vv*z - 4*d**3*g*p*ww*z + 8*d**3*g*s*vv*z - 4*d**3*g*s*ww*z - 4*d**3*g*s*yy*z + 4*d**3*g*vv*z**2 - 2*d**3*g*ww*z**2 - 2*d**3*g*yy*z**2 - 2*d**3*h*p**2*r + 2*d**3*h*p**2*ww - 4*d**3*h*p*s*vv + 4*d**3*h*p*s*ww - 4*d**3*h*p*vv*z + 4*d**3*h*p*ww*z - 8*d**3*h*s*vv*z + 4*d**3*h*s*ww*z + 4*d**3*h*s*yy*z - 4*d**3*h*vv*z**2 + 2*d**3*h*ww*z**2 + 2*d**3*h*yy*z**2 - 4*d**3*kk*p*q*s - 4*d**3*kk*p*q*z + 4*d**3*kk*p*r*s + 4*d**3*kk*p*r*z - 8*d**3*kk*q*s*z - 4*d**3*kk*q*z**2 + 8*d**3*kk*r*s*z + 4*d**3*kk*r*z**2 + 2*d**3*m*p**2*ww - 4*d**3*m*p*s*vv + 4*d**3*m*p*s*ww - 4*d**3*m*p*vv*z + 4*d**3*m*p*ww*z - 8*d**3*m*s*vv*z + 4*d**3*m*s*ww*z + 4*d**3*m*s*yy*z - 4*d**3*m*vv*z**2 + 2*d**3*m*ww*z**2 + 2*d**3*m*yy*z**2 - 2*d**3*n*p**2*ww + 4*d**3*n*p*s*vv - 4*d**3*n*p*s*ww + 4*d**3*n*p*vv*z - 4*d**3*n*p*ww*z + 8*d**3*n*s*vv*z - 4*d**3*n*s*ww*z - 4*d**3*n*s*yy*z + 4*d**3*n*vv*z**2 - 2*d**3*n*ww*z**2 - 2*d**3*n*yy*z**2 + 2*d**3*p**2*q*xx - 2*d**3*p**2*r*xx + 4*d**3*p*q*s*xx + 4*d**3*p*q*xx*z - 4*d**3*p*r*s*xx - 4*d**3*p*r*xx*z + 4*d**3*q*s*uu*z + 4*d**3*q*s*xx*z + 2*d**3*q*uu*z**2 + 2*d**3*q*xx*z**2 - 4*d**3*r*s*uu*z - 4*d**3*r*s*xx*z - 2*d**3*r*uu*z**2 - 2*d**3*r*xx*z**2 + 2*d**2*f*g*p**2*s + 2*d**2*f*kk*p*s**2 + 4*d**2*f*kk*p*s*z + 4*d**2*f*kk*s**2*z + 4*d**2*f*kk*s*z**2 - 2*d**2*f*p**2*s*xx - 2*d**2*f*p*s**2*xx - 4*d**2*f*p*s*xx*z - 2*d**2*f*s**2*uu*z - 2*d**2*f*s**2*xx*z - 2*d**2*f*s*uu*z**2 - 2*d**2*f*s*xx*z**2 - 12*d**2*g*p**2*q*s + 12*d**2*g*p**2*r*s - 2*d**2*g*p**2*s*ww + 2*d**2*g*p*s**2*vv - 2*d**2*g*p*s**2*ww + 4*d**2*g*p*s*vv*z - 4*d**2*g*p*s*ww*z + 4*d**2*g*s**2*vv*z - 2*d**2*g*s**2*ww*z - 2*d**2*g*s**2*yy*z + 4*d**2*g*s*vv*z**2 - 2*d**2*g*s*ww*z**2 - 2*d**2*g*s*yy*z**2 + 8*d**2*h*p**2*q*s - 12*d**2*h*p**2*r*s + 4*d**2*h*p**2*s*ww - 4*d**2*h*p*s**2*vv + 4*d**2*h*p*s**2*ww - 8*d**2*h*p*s*vv*z + 8*d**2*h*p*s*ww*z - 8*d**2*h*s**2*vv*z + 4*d**2*h*s**2*ww*z + 4*d**2*h*s**2*yy*z - 8*d**2*h*s*vv*z**2 + 4*d**2*h*s*ww*z**2 + 4*d**2*h*s*yy*z**2 - 4*d**2*kk*p*q*s**2 - 8*d**2*kk*p*q*s*z + 2*d**2*kk*p*r*s**2 + 4*d**2*kk*p*r*s*z - 8*d**2*kk*q*s**2*z - 8*d**2*kk*q*s*z**2 + 4*d**2*kk*r*s**2*z + 4*d**2*kk*r*s*z**2 + 2*d**2*l*p**2*r*s - 2*d**2*l*p**2*s*ww + 2*d**2*l*p*s**2*vv - 2*d**2*l*p*s**2*ww + 4*d**2*l*p*s*vv*z - 4*d**2*l*p*s*ww*z + 4*d**2*l*s**2*vv*z - 2*d**2*l*s**2*ww*z - 2*d**2*l*s**2*yy*z + 4*d**2*l*s*vv*z**2 - 2*d**2*l*s*ww*z**2 - 2*d**2*l*s*yy*z**2 + 2*d**2*m*p**2*s*ww - 2*d**2*m*p*s**2*vv + 2*d**2*m*p*s**2*ww - 4*d**2*m*p*s*vv*z + 4*d**2*m*p*s*ww*z - 4*d**2*m*s**2*vv*z + 2*d**2*m*s**2*ww*z + 2*d**2*m*s**2*yy*z - 4*d**2*m*s*vv*z**2 + 2*d**2*m*s*ww*z**2 + 2*d**2*m*s*yy*z**2 - 4*d**2*n*p**2*s*ww + 4*d**2*n*p*s**2*vv - 4*d**2*n*p*s**2*ww + 8*d**2*n*p*s*vv*z - 8*d**2*n*p*s*ww*z + 8*d**2*n*s**2*vv*z - 4*d**2*n*s**2*ww*z - 4*d**2*n*s**2*yy*z + 8*d**2*n*s*vv*z**2 - 4*d**2*n*s*ww*z**2 - 4*d**2*n*s*yy*z**2 + 2*d**2*o*p**2*s*ww - 2*d**2*o*p*s**2*vv + 2*d**2*o*p*s**2*ww - 4*d**2*o*p*s*vv*z + 4*d**2*o*p*s*ww*z - 4*d**2*o*s**2*vv*z + 2*d**2*o*s**2*ww*z + 2*d**2*o*s**2*yy*z - 4*d**2*o*s*vv*z**2 + 2*d**2*o*s*ww*z**2 + 2*d**2*o*s*yy*z**2 + 4*d**2*p**2*q*s*xx - 2*d**2*p**2*r*s*xx + 4*d**2*p*q*s**2*xx + 8*d**2*p*q*s*xx*z - 2*d**2*p*r*s**2*xx - 4*d**2*p*r*s*xx*z + 4*d**2*q*s**2*uu*z + 4*d**2*q*s**2*xx*z + 4*d**2*q*s*uu*z**2 + 4*d**2*q*s*xx*z**2 - 2*d**2*r*s**2*uu*z - 2*d**2*r*s**2*xx*z - 2*d**2*r*s*uu*z**2 - 2*d**2*r*s*xx*z**2 + 6*d*f*g*p**2*s**2 - 6*d*f*h*p**2*s**2 - 18*d*g*p**2*q*s**2 + 12*d*g*p**2*r*s**2 + 24*d*h*p**2*q*s**2 - 18*d*h*p**2*r*s**2 - 6*d*l*p**2*q*s**2 + 6*d*l*p**2*r*s**2 + 4*f*g*p**2*s**3 - 8*f*h*p**2*s**3 + 4*f*l*p**2*s**3 - 8*g*p**2*q*s**3 + 4*g*p**2*r*s**3 + 16*h*p**2*q*s**3 - 8*h*p**2*r*s**3 - 8*l*p**2*q*s**3 + 4*l*p**2*r*s**3) / (d**4*p**2)
    a2 = (+2*a*d**4*kk - a*d**4*uu - a*d**4*xx + 4*a*d**3*kk*p + 4*a*d**3*kk*s + 8*a*d**3*kk*z - 4*a*d**3*p*xx - 2*a*d**3*s*uu - 2*a*d**3*s*xx - 4*a*d**3*uu*z - 4*a*d**3*xx*z + 4*a*d**2*kk*p*s + 2*a*d**2*kk*p*z + 2*a*d**2*kk*s**2 + 8*a*d**2*kk*s*z + 2*a*d**2*kk*z**2 + 6*a*d**2*m*p**2 - 6*a*d**2*n*p**2 + a*d**2*o*p**2 - a*d**2*p**2*xx - 4*a*d**2*p*s*xx - 2*a*d**2*p*xx*z - a*d**2*s**2*uu - a*d**2*s**2*xx - 4*a*d**2*s*uu*z - 4*a*d**2*s*xx*z - a*d**2*uu*z**2 - a*d**2*xx*z**2 + 12*a*d*m*p**2*s - 18*a*d*n*p**2*s + 6*a*d*o*p**2*s + 6*a*m*p**2*s**2 - 12*a*n*p**2*s**2 + 6*a*o*p**2*s**2 - 4*b*d**3*kk*p - 4*b*d**3*kk*s - 8*b*d**3*kk*z + 4*b*d**3*p*xx + 2*b*d**3*s*uu + 2*b*d**3*s*xx + 4*b*d**3*uu*z + 4*b*d**3*xx*z - 8*b*d**2*kk*p*s - 4*b*d**2*kk*p*z - 4*b*d**2*kk*s**2 - 16*b*d**2*kk*s*z - 4*b*d**2*kk*z**2 - 6*b*d**2*m*p**2 + 4*b*d**2*n*p**2 + 2*b*d**2*p**2*xx + 8*b*d**2*p*s*xx + 4*b*d**2*p*xx*z + 2*b*d**2*s**2*uu + 2*b*d**2*s**2*xx + 8*b*d**2*s*uu*z + 8*b*d**2*s*xx*z + 2*b*d**2*uu*z**2 + 2*b*d**2*xx*z**2 - 18*b*d*m*p**2*s + 24*b*d*n*p**2*s - 6*b*d*o*p**2*s - 12*b*m*p**2*s**2 + 24*b*n*p**2*s**2 - 12*b*o*p**2*s**2 + 4*c*d**2*kk*p*s + 2*c*d**2*kk*p*z + 2*c*d**2*kk*s**2 + 8*c*d**2*kk*s*z + 2*c*d**2*kk*z**2 + c*d**2*m*p**2 - c*d**2*p**2*xx - 4*c*d**2*p*s*xx - 2*c*d**2*p*xx*z - c*d**2*s**2*uu - c*d**2*s**2*xx - 4*c*d**2*s*uu*z - 4*c*d**2*s*xx*z - c*d**2*uu*z**2 - c*d**2*xx*z**2 + 6*c*d*m*p**2*s - 6*c*d*n*p**2*s + 6*c*m*p**2*s**2 - 12*c*n*p**2*s**2 + 6*c*o*p**2*s**2 - 2*d**4*g*vv + d**4*g*ww + d**4*g*yy - 2*d**4*kk*r + 2*d**4*m*vv - d**4*m*ww - d**4*m*yy + d**4*r*uu + d**4*r*xx - 4*d**3*g*p*vv + 4*d**3*g*p*ww - 4*d**3*g*s*vv + 2*d**3*g*s*ww + 2*d**3*g*s*yy - 8*d**3*g*vv*z + 4*d**3*g*ww*z + 4*d**3*g*yy*z + 4*d**3*h*p*vv - 4*d**3*h*p*ww + 4*d**3*h*s*vv - 2*d**3*h*s*ww - 2*d**3*h*s*yy + 8*d**3*h*vv*z - 4*d**3*h*ww*z - 4*d**3*h*yy*z + 4*d**3*kk*p*q - 4*d**3*kk*p*r + 4*d**3*kk*q*s + 8*d**3*kk*q*z - 4*d**3*kk*r*s - 8*d**3*kk*r*z + 4*d**3*m*p*vv - 4*d**3*m*p*ww + 4*d**3*m*s*vv - 2*d**3*m*s*ww - 2*d**3*m*s*yy + 8*d**3*m*vv*z - 4*d**3*m*ww*z - 4*d**3*m*yy*z - 4*d**3*n*p*vv + 4*d**3*n*p*ww - 4*d**3*n*s*vv + 2*d**3*n*s*ww + 2*d**3*n*s*yy - 8*d**3*n*vv*z + 4*d**3*n*ww*z + 4*d**3*n*yy*z - 4*d**3*p*q*xx + 4*d**3*p*r*xx - 2*d**3*q*s*uu - 2*d**3*q*s*xx - 4*d**3*q*uu*z - 4*d**3*q*xx*z + 2*d**3*r*s*uu + 2*d**3*r*s*xx + 4*d**3*r*uu*z + 4*d**3*r*xx*z - d**2*f*g*p**2 - 4*d**2*f*kk*p*s - 2*d**2*f*kk*p*z - 2*d**2*f*kk*s**2 - 8*d**2*f*kk*s*z - 2*d**2*f*kk*z**2 + d**2*f*p**2*xx + 4*d**2*f*p*s*xx + 2*d**2*f*p*xx*z + d**2*f*s**2*uu + d**2*f*s**2*xx + 4*d**2*f*s*uu*z + 4*d**2*f*s*xx*z + d**2*f*uu*z**2 + d**2*f*xx*z**2 + 6*d**2*g*p**2*q - 6*d**2*g*p**2*r + d**2*g*p**2*ww - 4*d**2*g*p*s*vv + 4*d**2*g*p*s*ww - 2*d**2*g*p*vv*z + 2*d**2*g*p*ww*z - 2*d**2*g*s**2*vv + d**2*g*s**2*ww + d**2*g*s**2*yy - 8*d**2*g*s*vv*z + 4*d**2*g*s*ww*z + 4*d**2*g*s*yy*z - 2*d**2*g*vv*z**2 + d**2*g*ww*z**2 + d**2*g*yy*z**2 - 4*d**2*h*p**2*q + 6*d**2*h*p**2*r - 2*d**2*h*p**2*ww + 8*d**2*h*p*s*vv - 8*d**2*h*p*s*ww + 4*d**2*h*p*vv*z - 4*d**2*h*p*ww*z + 4*d**2*h*s**2*vv - 2*d**2*h*s**2*ww - 2*d**2*h*s**2*yy + 16*d**2*h*s*vv*z - 8*d**2*h*s*ww*z - 8*d**2*h*s*yy*z + 4*d**2*h*vv*z**2 - 2*d**2*h*ww*z**2 - 2*d**2*h*yy*z**2 + 8*d**2*kk*p*q*s + 4*d**2*kk*p*q*z - 4*d**2*kk*p*r*s - 2*d**2*kk*p*r*z + 4*d**2*kk*q*s**2 + 16*d**2*kk*q*s*z + 4*d**2*kk*q*z**2 - 2*d**2*kk*r*s**2 - 8*d**2*kk*r*s*z - 2*d**2*kk*r*z**2 - d**2*l*p**2*r + d**2*l*p**2*ww - 4*d**2*l*p*s*vv + 4*d**2*l*p*s*ww - 2*d**2*l*p*vv*z + 2*d**2*l*p*ww*z - 2*d**2*l*s**2*vv + d**2*l*s**2*ww + d**2*l*s**2*yy - 8*d**2*l*s*vv*z + 4*d**2*l*s*ww*z + 4*d**2*l*s*yy*z - 2*d**2*l*vv*z**2 + d**2*l*ww*z**2 + d**2*l*yy*z**2 - d**2*m*p**2*ww + 4*d**2*m*p*s*vv - 4*d**2*m*p*s*ww + 2*d**2*m*p*vv*z - 2*d**2*m*p*ww*z + 2*d**2*m*s**2*vv - d**2*m*s**2*ww - d**2*m*s**2*yy + 8*d**2*m*s*vv*z - 4*d**2*m*s*ww*z - 4*d**2*m*s*yy*z + 2*d**2*m*vv*z**2 - d**2*m*ww*z**2 - d**2*m*yy*z**2 + 2*d**2*n*p**2*ww - 8*d**2*n*p*s*vv + 8*d**2*n*p*s*ww - 4*d**2*n*p*vv*z + 4*d**2*n*p*ww*z - 4*d**2*n*s**2*vv + 2*d**2*n*s**2*ww + 2*d**2*n*s**2*yy - 16*d**2*n*s*vv*z + 8*d**2*n*s*ww*z + 8*d**2*n*s*yy*z - 4*d**2*n*vv*z**2 + 2*d**2*n*ww*z**2 + 2*d**2*n*yy*z**2 - d**2*o*p**2*ww + 4*d**2*o*p*s*vv - 4*d**2*o*p*s*ww + 2*d**2*o*p*vv*z - 2*d**2*o*p*ww*z + 2*d**2*o*s**2*vv - d**2*o*s**2*ww - d**2*o*s**2*yy + 8*d**2*o*s*vv*z - 4*d**2*o*s*ww*z - 4*d**2*o*s*yy*z + 2*d**2*o*vv*z**2 - d**2*o*ww*z**2 - d**2*o*yy*z**2 - 2*d**2*p**2*q*xx + d**2*p**2*r*xx - 8*d**2*p*q*s*xx - 4*d**2*p*q*xx*z + 4*d**2*p*r*s*xx + 2*d**2*p*r*xx*z - 2*d**2*q*s**2*uu - 2*d**2*q*s**2*xx - 8*d**2*q*s*uu*z - 8*d**2*q*s*xx*z - 2*d**2*q*uu*z**2 - 2*d**2*q*xx*z**2 + d**2*r*s**2*uu + d**2*r*s**2*xx + 4*d**2*r*s*uu*z + 4*d**2*r*s*xx*z + d**2*r*uu*z**2 + d**2*r*xx*z**2 - 6*d*f*g*p**2*s + 6*d*f*h*p**2*s + 18*d*g*p**2*q*s - 12*d*g*p**2*r*s - 24*d*h*p**2*q*s + 18*d*h*p**2*r*s + 6*d*l*p**2*q*s - 6*d*l*p**2*r*s - 6*f*g*p**2*s**2 + 12*f*h*p**2*s**2 - 6*f*l*p**2*s**2 + 12*g*p**2*q*s**2 - 6*g*p**2*r*s**2 - 24*h*p**2*q*s**2 + 12*h*p**2*r*s**2 + 12*l*p**2*q*s**2 - 6*l*p**2*r*s**2) / (d**4*p**2)
    a3 = (-4*a*d**3*kk + 2*a*d**3*uu + 2*a*d**3*xx - 2*a*d**2*kk*p - 4*a*d**2*kk*s - 4*a*d**2*kk*z + 2*a*d**2*p*xx + 2*a*d**2*s*uu + 2*a*d**2*s*xx + 2*a*d**2*uu*z + 2*a*d**2*xx*z - 4*a*d*m*p**2 + 6*a*d*n*p**2 - 2*a*d*o*p**2 - 4*a*m*p**2*s + 8*a*n*p**2*s - 4*a*o*p**2*s + 4*b*d**3*kk - 2*b*d**3*uu - 2*b*d**3*xx + 4*b*d**2*kk*p + 8*b*d**2*kk*s + 8*b*d**2*kk*z - 4*b*d**2*p*xx - 4*b*d**2*s*uu - 4*b*d**2*s*xx - 4*b*d**2*uu*z - 4*b*d**2*xx*z + 6*b*d*m*p**2 - 8*b*d*n*p**2 + 2*b*d*o*p**2 + 8*b*m*p**2*s - 16*b*n*p**2*s + 8*b*o*p**2*s - 2*c*d**2*kk*p - 4*c*d**2*kk*s - 4*c*d**2*kk*z + 2*c*d**2*p*xx + 2*c*d**2*s*uu + 2*c*d**2*s*xx + 2*c*d**2*uu*z + 2*c*d**2*xx*z - 2*c*d*m*p**2 + 2*c*d*n*p**2 - 4*c*m*p**2*s + 8*c*n*p**2*s - 4*c*o*p**2*s + 4*d**3*g*vv - 2*d**3*g*ww - 2*d**3*g*yy - 4*d**3*h*vv + 2*d**3*h*ww + 2*d**3*h*yy - 4*d**3*kk*q + 4*d**3*kk*r - 4*d**3*m*vv + 2*d**3*m*ww + 2*d**3*m*yy + 4*d**3*n*vv - 2*d**3*n*ww - 2*d**3*n*yy + 2*d**3*q*uu + 2*d**3*q*xx - 2*d**3*r*uu - 2*d**3*r*xx + 2*d**2*f*kk*p + 4*d**2*f*kk*s + 4*d**2*f*kk*z - 2*d**2*f*p*xx - 2*d**2*f*s*uu - 2*d**2*f*s*xx - 2*d**2*f*uu*z - 2*d**2*f*xx*z + 2*d**2*g*p*vv - 2*d**2*g*p*ww + 4*d**2*g*s*vv - 2*d**2*g*s*ww - 2*d**2*g*s*yy + 4*d**2*g*vv*z - 2*d**2*g*ww*z - 2*d**2*g*yy*z - 4*d**2*h*p*vv + 4*d**2*h*p*ww - 8*d**2*h*s*vv + 4*d**2*h*s*ww + 4*d**2*h*s*yy - 8*d**2*h*vv*z + 4*d**2*h*ww*z + 4*d**2*h*yy*z - 4*d**2*kk*p*q + 2*d**2*kk*p*r - 8*d**2*kk*q*s - 8*d**2*kk*q*z + 4*d**2*kk*r*s + 4*d**2*kk*r*z + 2*d**2*l*p*vv - 2*d**2*l*p*ww + 4*d**2*l*s*vv - 2*d**2*l*s*ww - 2*d**2*l*s*yy + 4*d**2*l*vv*z - 2*d**2*l*ww*z - 2*d**2*l*yy*z - 2*d**2*m*p*vv + 2*d**2*m*p*ww - 4*d**2*m*s*vv + 2*d**2*m*s*ww + 2*d**2*m*s*yy - 4*d**2*m*vv*z + 2*d**2*m*ww*z + 2*d**2*m*yy*z + 4*d**2*n*p*vv - 4*d**2*n*p*ww + 8*d**2*n*s*vv - 4*d**2*n*s*ww - 4*d**2*n*s*yy + 8*d**2*n*vv*z - 4*d**2*n*ww*z - 4*d**2*n*yy*z - 2*d**2*o*p*vv + 2*d**2*o*p*ww - 4*d**2*o*s*vv + 2*d**2*o*s*ww + 2*d**2*o*s*yy - 4*d**2*o*vv*z + 2*d**2*o*ww*z + 2*d**2*o*yy*z + 4*d**2*p*q*xx - 2*d**2*p*r*xx + 4*d**2*q*s*uu + 4*d**2*q*s*xx + 4*d**2*q*uu*z + 4*d**2*q*xx*z - 2*d**2*r*s*uu - 2*d**2*r*s*xx - 2*d**2*r*uu*z - 2*d**2*r*xx*z + 2*d*f*g*p**2 - 2*d*f*h*p**2 - 6*d*g*p**2*q + 4*d*g*p**2*r + 8*d*h*p**2*q - 6*d*h*p**2*r - 2*d*l*p**2*q + 2*d*l*p**2*r + 4*f*g*p**2*s - 8*f*h*p**2*s + 4*f*l*p**2*s - 8*g*p**2*q*s + 4*g*p**2*r*s + 16*h*p**2*q*s - 8*h*p**2*r*s - 8*l*p**2*q*s + 4*l*p**2*r*s) / (d**4*p**2)
    a4 = (+2*a*d**2*kk - a*d**2*uu - a*d**2*xx + a*m*p**2 - 2*a*n*p**2 + a*o*p**2 - 4*b*d**2*kk + 2*b*d**2*uu + 2*b*d**2*xx - 2*b*m*p**2 + 4*b*n*p**2 - 2*b*o*p**2 + 2*c*d**2*kk - c*d**2*uu - c*d**2*xx + c*m*p**2 - 2*c*n*p**2 + c*o*p**2 - 2*d**2*f*kk + d**2*f*uu + d**2*f*xx - 2*d**2*g*vv + d**2*g*ww + d**2*g*yy + 4*d**2*h*vv - 2*d**2*h*ww - 2*d**2*h*yy + 4*d**2*kk*q - 2*d**2*kk*r - 2*d**2*l*vv + d**2*l*ww + d**2*l*yy + 2*d**2*m*vv - d**2*m*ww - d**2*m*yy - 4*d**2*n*vv + 2*d**2*n*ww + 2*d**2*n*yy + 2*d**2*o*vv - d**2*o*ww - d**2*o*yy - 2*d**2*q*uu - 2*d**2*q*xx + d**2*r*uu + d**2*r*xx - f*g*p**2 + 2*f*h*p**2 - f*l*p**2 + 2*g*p**2*q - g*p**2*r - 4*h*p**2*q + 2*h*p**2*r + 2*l*p**2*q - l*p**2*r) / (d**4*p**2)
    """

    """
    a0 = ((+2*a*d**4*kk*p*z + 2*a*d**4*kk*z**2 + a*d**4*m*p**2 - a*d**4*p**2*xx - 2*a*d**4*p*xx*z - a*d**4*uu*z**2 - a*d**4*xx*z**2 + 4*a*d**3*kk*p*s*z + 4*a*d**3*kk*s*z**2 + 4*a*d**3*m*p**2*s - 2*a*d**3*n*p**2*s - 2*a*d**3*p**2*s*xx - 4*a*d**3*p*s*xx*z - 2*a*d**3*s*uu*z**2 - 2*a*d**3*s*xx*z**2 + 2*a*d**2*kk*p*s**2*z + 2*a*d**2*kk*s**2*z**2 + 6*a*d**2*m*p**2*s**2 - 6*a*d**2*n*p**2*s**2 + a*d**2*o*p**2*s**2 - a*d**2*p**2*s**2*xx - 2*a*d**2*p*s**2*xx*z - a*d**2*s**2*uu*z**2 - a*d**2*s**2*xx*z**2 + 4*a*d*m*p**2*s**3 - 6*a*d*n*p**2*s**3 + 2*a*d*o*p**2*s**3 + a*m*p**2*s**4 - 2*a*n*p**2*s**4 + a*o*p**2*s**4 - 4*b*d**3*kk*p*s*z - 4*b*d**3*kk*s*z**2 - 2*b*d**3*m*p**2*s + 2*b*d**3*p**2*s*xx + 4*b*d**3*p*s*xx*z + 2*b*d**3*s*uu*z**2 + 2*b*d**3*s*xx*z**2 - 4*b*d**2*kk*p*s**2*z - 4*b*d**2*kk*s**2*z**2 - 6*b*d**2*m*p**2*s**2 + 4*b*d**2*n*p**2*s**2 + 2*b*d**2*p**2*s**2*xx + 4*b*d**2*p*s**2*xx*z + 2*b*d**2*s**2*uu*z**2 + 2*b*d**2*s**2*xx*z**2 - 6*b*d*m*p**2*s**3 + 8*b*d*n*p**2*s**3 - 2*b*d*o*p**2*s**3 - 2*b*m*p**2*s**4 + 4*b*n*p**2*s**4 - 2*b*o*p**2*s**4 + 2*c*d**2*kk*p*s**2*z + 2*c*d**2*kk*s**2*z**2 + c*d**2*m*p**2*s**2 - c*d**2*p**2*s**2*xx - 2*c*d**2*p*s**2*xx*z - c*d**2*s**2*uu*z**2 - c*d**2*s**2*xx*z**2 + 2*c*d*m*p**2*s**3 - 2*c*d*n*p**2*s**3 + c*m*p**2*s**4 - 2*c*n*p**2*s**4 + c*o*p**2*s**4 - d**4*g*p**2*r + d**4*g*p**2*ww - 2*d**4*g*p*vv*z + 2*d**4*g*p*ww*z - 2*d**4*g*vv*z**2 + d**4*g*ww*z**2 + d**4*g*yy*z**2 - 2*d**4*kk*p*r*z - 2*d**4*kk*r*z**2 - d**4*m*p**2*ww + 2*d**4*m*p*vv*z - 2*d**4*m*p*ww*z + 2*d**4*m*vv*z**2 - d**4*m*ww*z**2 - d**4*m*yy*z**2 + d**4*p**2*r*xx + 2*d**4*p*r*xx*z + d**4*r*uu*z**2 + d**4*r*xx*z**2 + 2*d**3*g*p**2*q*s - 4*d**3*g*p**2*r*s + 2*d**3*g*p**2*s*ww - 4*d**3*g*p*s*vv*z + 4*d**3*g*p*s*ww*z - 4*d**3*g*s*vv*z**2 + 2*d**3*g*s*ww*z**2 + 2*d**3*g*s*yy*z**2 + 2*d**3*h*p**2*r*s - 2*d**3*h*p**2*s*ww + 4*d**3*h*p*s*vv*z - 4*d**3*h*p*s*ww*z + 4*d**3*h*s*vv*z**2 - 2*d**3*h*s*ww*z**2 - 2*d**3*h*s*yy*z**2 + 4*d**3*kk*p*q*s*z - 4*d**3*kk*p*r*s*z + 4*d**3*kk*q*s*z**2 - 4*d**3*kk*r*s*z**2 - 2*d**3*m*p**2*s*ww + 4*d**3*m*p*s*vv*z - 4*d**3*m*p*s*ww*z + 4*d**3*m*s*vv*z**2 - 2*d**3*m*s*ww*z**2 - 2*d**3*m*s*yy*z**2 + 2*d**3*n*p**2*s*ww - 4*d**3*n*p*s*vv*z + 4*d**3*n*p*s*ww*z - 4*d**3*n*s*vv*z**2 + 2*d**3*n*s*ww*z**2 + 2*d**3*n*s*yy*z**2 - 2*d**3*p**2*q*s*xx + 2*d**3*p**2*r*s*xx - 4*d**3*p*q*s*xx*z + 4*d**3*p*r*s*xx*z - 2*d**3*q*s*uu*z**2 - 2*d**3*q*s*xx*z**2 + 2*d**3*r*s*uu*z**2 + 2*d**3*r*s*xx*z**2 - d**2*f*g*p**2*s**2 - 2*d**2*f*kk*p*s**2*z - 2*d**2*f*kk*s**2*z**2 + d**2*f*p**2*s**2*xx + 2*d**2*f*p*s**2*xx*z + d**2*f*s**2*uu*z**2 + d**2*f*s**2*xx*z**2 + 6*d**2*g*p**2*q*s**2 - 6*d**2*g*p**2*r*s**2 + d**2*g*p**2*s**2*ww - 2*d**2*g*p*s**2*vv*z + 2*d**2*g*p*s**2*ww*z - 2*d**2*g*s**2*vv*z**2 + d**2*g*s**2*ww*z**2 + d**2*g*s**2*yy*z**2 - 4*d**2*h*p**2*q*s**2 + 6*d**2*h*p**2*r*s**2 - 2*d**2*h*p**2*s**2*ww + 4*d**2*h*p*s**2*vv*z - 4*d**2*h*p*s**2*ww*z + 4*d**2*h*s**2*vv*z**2 - 2*d**2*h*s**2*ww*z**2 - 2*d**2*h*s**2*yy*z**2 + 4*d**2*kk*p*q*s**2*z - 2*d**2*kk*p*r*s**2*z + 4*d**2*kk*q*s**2*z**2 - 2*d**2*kk*r*s**2*z**2 - d**2*l*p**2*r*s**2 + d**2*l*p**2*s**2*ww - 2*d**2*l*p*s**2*vv*z + 2*d**2*l*p*s**2*ww*z - 2*d**2*l*s**2*vv*z**2 + d**2*l*s**2*ww*z**2 + d**2*l*s**2*yy*z**2 - d**2*m*p**2*s**2*ww + 2*d**2*m*p*s**2*vv*z - 2*d**2*m*p*s**2*ww*z + 2*d**2*m*s**2*vv*z**2 - d**2*m*s**2*ww*z**2 - d**2*m*s**2*yy*z**2 + 2*d**2*n*p**2*s**2*ww - 4*d**2*n*p*s**2*vv*z + 4*d**2*n*p*s**2*ww*z - 4*d**2*n*s**2*vv*z**2 + 2*d**2*n*s**2*ww*z**2 + 2*d**2*n*s**2*yy*z**2 - d**2*o*p**2*s**2*ww + 2*d**2*o*p*s**2*vv*z - 2*d**2*o*p*s**2*ww*z + 2*d**2*o*s**2*vv*z**2 - d**2*o*s**2*ww*z**2 - d**2*o*s**2*yy*z**2 - 2*d**2*p**2*q*s**2*xx + d**2*p**2*r*s**2*xx - 4*d**2*p*q*s**2*xx*z + 2*d**2*p*r*s**2*xx*z - 2*d**2*q*s**2*uu*z**2 - 2*d**2*q*s**2*xx*z**2 + d**2*r*s**2*uu*z**2 + d**2*r*s**2*xx*z**2 - 2*d*f*g*p**2*s**3 + 2*d*f*h*p**2*s**3 + 6*d*g*p**2*q*s**3 - 4*d*g*p**2*r*s**3 - 8*d*h*p**2*q*s**3 + 6*d*h*p**2*r*s**3 + 2*d*l*p**2*q*s**3 - 2*d*l*p**2*r*s**3 - f*g*p**2*s**4 + 2*f*h*p**2*s**4 - f*l*p**2*s**4 + 2*g*p**2*q*s**4 - g*p**2*r*s**4 - 4*h*p**2*q*s**4 + 2*h*p**2*r*s**4 + 2*l*p**2*q*s**4 - l*p**2*r*s**4) + (+2*a*d**4*k*p*z + 2*a*d**4*k*z**2 + a*d**4*m*p**2 - a*d**4*p**2*x - 2*a*d**4*p*x*z - a*d**4*u*z**2 - a*d**4*x*z**2 + 4*a*d**3*k*p*s*z + 4*a*d**3*k*s*z**2 + 4*a*d**3*m*p**2*s - 2*a*d**3*n*p**2*s - 2*a*d**3*p**2*s*x - 4*a*d**3*p*s*x*z - 2*a*d**3*s*u*z**2 - 2*a*d**3*s*x*z**2 + 2*a*d**2*k*p*s**2*z + 2*a*d**2*k*s**2*z**2 + 6*a*d**2*m*p**2*s**2 - 6*a*d**2*n*p**2*s**2 + a*d**2*o*p**2*s**2 - a*d**2*p**2*s**2*x - 2*a*d**2*p*s**2*x*z - a*d**2*s**2*u*z**2 - a*d**2*s**2*x*z**2 + 4*a*d*m*p**2*s**3 - 6*a*d*n*p**2*s**3 + 2*a*d*o*p**2*s**3 + a*m*p**2*s**4 - 2*a*n*p**2*s**4 + a*o*p**2*s**4 - 4*b*d**3*k*p*s*z - 4*b*d**3*k*s*z**2 - 2*b*d**3*m*p**2*s + 2*b*d**3*p**2*s*x + 4*b*d**3*p*s*x*z + 2*b*d**3*s*u*z**2 + 2*b*d**3*s*x*z**2 - 4*b*d**2*k*p*s**2*z - 4*b*d**2*k*s**2*z**2 - 6*b*d**2*m*p**2*s**2 + 4*b*d**2*n*p**2*s**2 + 2*b*d**2*p**2*s**2*x + 4*b*d**2*p*s**2*x*z + 2*b*d**2*s**2*u*z**2 + 2*b*d**2*s**2*x*z**2 - 6*b*d*m*p**2*s**3 + 8*b*d*n*p**2*s**3 - 2*b*d*o*p**2*s**3 - 2*b*m*p**2*s**4 + 4*b*n*p**2*s**4 - 2*b*o*p**2*s**4 + 2*c*d**2*k*p*s**2*z + 2*c*d**2*k*s**2*z**2 + c*d**2*m*p**2*s**2 - c*d**2*p**2*s**2*x - 2*c*d**2*p*s**2*x*z - c*d**2*s**2*u*z**2 - c*d**2*s**2*x*z**2 + 2*c*d*m*p**2*s**3 - 2*c*d*n*p**2*s**3 + c*m*p**2*s**4 - 2*c*n*p**2*s**4 + c*o*p**2*s**4 - d**4*g*p**2*r + d**4*g*p**2*w - 2*d**4*g*p*v*z + 2*d**4*g*p*w*z - 2*d**4*g*v*z**2 + d**4*g*w*z**2 + d**4*g*y*z**2 - 2*d**4*k*p*r*z - 2*d**4*k*r*z**2 - d**4*m*p**2*w + 2*d**4*m*p*v*z - 2*d**4*m*p*w*z + 2*d**4*m*v*z**2 - d**4*m*w*z**2 - d**4*m*y*z**2 + d**4*p**2*r*x + 2*d**4*p*r*x*z + d**4*r*u*z**2 + d**4*r*x*z**2 + 2*d**3*g*p**2*q*s - 4*d**3*g*p**2*r*s + 2*d**3*g*p**2*s*w - 4*d**3*g*p*s*v*z + 4*d**3*g*p*s*w*z - 4*d**3*g*s*v*z**2 + 2*d**3*g*s*w*z**2 + 2*d**3*g*s*y*z**2 + 2*d**3*h*p**2*r*s - 2*d**3*h*p**2*s*w + 4*d**3*h*p*s*v*z - 4*d**3*h*p*s*w*z + 4*d**3*h*s*v*z**2 - 2*d**3*h*s*w*z**2 - 2*d**3*h*s*y*z**2 + 4*d**3*k*p*q*s*z - 4*d**3*k*p*r*s*z + 4*d**3*k*q*s*z**2 - 4*d**3*k*r*s*z**2 - 2*d**3*m*p**2*s*w + 4*d**3*m*p*s*v*z - 4*d**3*m*p*s*w*z + 4*d**3*m*s*v*z**2 - 2*d**3*m*s*w*z**2 - 2*d**3*m*s*y*z**2 + 2*d**3*n*p**2*s*w - 4*d**3*n*p*s*v*z + 4*d**3*n*p*s*w*z - 4*d**3*n*s*v*z**2 + 2*d**3*n*s*w*z**2 + 2*d**3*n*s*y*z**2 - 2*d**3*p**2*q*s*x + 2*d**3*p**2*r*s*x - 4*d**3*p*q*s*x*z + 4*d**3*p*r*s*x*z - 2*d**3*q*s*u*z**2 - 2*d**3*q*s*x*z**2 + 2*d**3*r*s*u*z**2 + 2*d**3*r*s*x*z**2 - d**2*f*g*p**2*s**2 - 2*d**2*f*k*p*s**2*z - 2*d**2*f*k*s**2*z**2 + d**2*f*p**2*s**2*x + 2*d**2*f*p*s**2*x*z + d**2*f*s**2*u*z**2 + d**2*f*s**2*x*z**2 + 6*d**2*g*p**2*q*s**2 - 6*d**2*g*p**2*r*s**2 + d**2*g*p**2*s**2*w - 2*d**2*g*p*s**2*v*z + 2*d**2*g*p*s**2*w*z - 2*d**2*g*s**2*v*z**2 + d**2*g*s**2*w*z**2 + d**2*g*s**2*y*z**2 - 4*d**2*h*p**2*q*s**2 + 6*d**2*h*p**2*r*s**2 - 2*d**2*h*p**2*s**2*w + 4*d**2*h*p*s**2*v*z - 4*d**2*h*p*s**2*w*z + 4*d**2*h*s**2*v*z**2 - 2*d**2*h*s**2*w*z**2 - 2*d**2*h*s**2*y*z**2 + 4*d**2*k*p*q*s**2*z - 2*d**2*k*p*r*s**2*z + 4*d**2*k*q*s**2*z**2 - 2*d**2*k*r*s**2*z**2 - d**2*l*p**2*r*s**2 + d**2*l*p**2*s**2*w - 2*d**2*l*p*s**2*v*z + 2*d**2*l*p*s**2*w*z - 2*d**2*l*s**2*v*z**2 + d**2*l*s**2*w*z**2 + d**2*l*s**2*y*z**2 - d**2*m*p**2*s**2*w + 2*d**2*m*p*s**2*v*z - 2*d**2*m*p*s**2*w*z + 2*d**2*m*s**2*v*z**2 - d**2*m*s**2*w*z**2 - d**2*m*s**2*y*z**2 + 2*d**2*n*p**2*s**2*w - 4*d**2*n*p*s**2*v*z + 4*d**2*n*p*s**2*w*z - 4*d**2*n*s**2*v*z**2 + 2*d**2*n*s**2*w*z**2 + 2*d**2*n*s**2*y*z**2 - d**2*o*p**2*s**2*w + 2*d**2*o*p*s**2*v*z - 2*d**2*o*p*s**2*w*z + 2*d**2*o*s**2*v*z**2 - d**2*o*s**2*w*z**2 - d**2*o*s**2*y*z**2 - 2*d**2*p**2*q*s**2*x + d**2*p**2*r*s**2*x - 4*d**2*p*q*s**2*x*z + 2*d**2*p*r*s**2*x*z - 2*d**2*q*s**2*u*z**2 - 2*d**2*q*s**2*x*z**2 + d**2*r*s**2*u*z**2 + d**2*r*s**2*x*z**2 - 2*d*f*g*p**2*s**3 + 2*d*f*h*p**2*s**3 + 6*d*g*p**2*q*s**3 - 4*d*g*p**2*r*s**3 - 8*d*h*p**2*q*s**3 + 6*d*h*p**2*r*s**3 + 2*d*l*p**2*q*s**3 - 2*d*l*p**2*r*s**3 - f*g*p**2*s**4 + 2*f*h*p**2*s**4 - f*l*p**2*s**4 + 2*g*p**2*q*s**4 - g*p**2*r*s**4 - 4*h*p**2*q*s**4 + 2*h*p**2*r*s**4 + 2*l*p**2*q*s**4 - l*p**2*r*s**4)) / (d**4*p**2)
    a1 = ((-2*a*d**4*kk*p - 4*a*d**4*kk*z + 2*a*d**4*p*xx + 2*a*d**4*uu*z + 2*a*d**4*xx*z - 4*a*d**3*kk*p*s - 4*a*d**3*kk*p*z - 8*a*d**3*kk*s*z - 4*a*d**3*kk*z**2 - 4*a*d**3*m*p**2 + 2*a*d**3*n*p**2 + 2*a*d**3*p**2*xx + 4*a*d**3*p*s*xx + 4*a*d**3*p*xx*z + 4*a*d**3*s*uu*z + 4*a*d**3*s*xx*z + 2*a*d**3*uu*z**2 + 2*a*d**3*xx*z**2 - 2*a*d**2*kk*p*s**2 - 4*a*d**2*kk*p*s*z - 4*a*d**2*kk*s**2*z - 4*a*d**2*kk*s*z**2 - 12*a*d**2*m*p**2*s + 12*a*d**2*n*p**2*s - 2*a*d**2*o*p**2*s + 2*a*d**2*p**2*s*xx + 2*a*d**2*p*s**2*xx + 4*a*d**2*p*s*xx*z + 2*a*d**2*s**2*uu*z + 2*a*d**2*s**2*xx*z + 2*a*d**2*s*uu*z**2 + 2*a*d**2*s*xx*z**2 - 12*a*d*m*p**2*s**2 + 18*a*d*n*p**2*s**2 - 6*a*d*o*p**2*s**2 - 4*a*m*p**2*s**3 + 8*a*n*p**2*s**3 - 4*a*o*p**2*s**3 + 4*b*d**3*kk*p*s + 4*b*d**3*kk*p*z + 8*b*d**3*kk*s*z + 4*b*d**3*kk*z**2 + 2*b*d**3*m*p**2 - 2*b*d**3*p**2*xx - 4*b*d**3*p*s*xx - 4*b*d**3*p*xx*z - 4*b*d**3*s*uu*z - 4*b*d**3*s*xx*z - 2*b*d**3*uu*z**2 - 2*b*d**3*xx*z**2 + 4*b*d**2*kk*p*s**2 + 8*b*d**2*kk*p*s*z + 8*b*d**2*kk*s**2*z + 8*b*d**2*kk*s*z**2 + 12*b*d**2*m*p**2*s - 8*b*d**2*n*p**2*s - 4*b*d**2*p**2*s*xx - 4*b*d**2*p*s**2*xx - 8*b*d**2*p*s*xx*z - 4*b*d**2*s**2*uu*z - 4*b*d**2*s**2*xx*z - 4*b*d**2*s*uu*z**2 - 4*b*d**2*s*xx*z**2 + 18*b*d*m*p**2*s**2 - 24*b*d*n*p**2*s**2 + 6*b*d*o*p**2*s**2 + 8*b*m*p**2*s**3 - 16*b*n*p**2*s**3 + 8*b*o*p**2*s**3 - 2*c*d**2*kk*p*s**2 - 4*c*d**2*kk*p*s*z - 4*c*d**2*kk*s**2*z - 4*c*d**2*kk*s*z**2 - 2*c*d**2*m*p**2*s + 2*c*d**2*p**2*s*xx + 2*c*d**2*p*s**2*xx + 4*c*d**2*p*s*xx*z + 2*c*d**2*s**2*uu*z + 2*c*d**2*s**2*xx*z + 2*c*d**2*s*uu*z**2 + 2*c*d**2*s*xx*z**2 - 6*c*d*m*p**2*s**2 + 6*c*d*n*p**2*s**2 - 4*c*m*p**2*s**3 + 8*c*n*p**2*s**3 - 4*c*o*p**2*s**3 + 2*d**4*g*p*vv - 2*d**4*g*p*ww + 4*d**4*g*vv*z - 2*d**4*g*ww*z - 2*d**4*g*yy*z + 2*d**4*kk*p*r + 4*d**4*kk*r*z - 2*d**4*m*p*vv + 2*d**4*m*p*ww - 4*d**4*m*vv*z + 2*d**4*m*ww*z + 2*d**4*m*yy*z - 2*d**4*p*r*xx - 2*d**4*r*uu*z - 2*d**4*r*xx*z - 2*d**3*g*p**2*q + 4*d**3*g*p**2*r - 2*d**3*g*p**2*ww + 4*d**3*g*p*s*vv - 4*d**3*g*p*s*ww + 4*d**3*g*p*vv*z - 4*d**3*g*p*ww*z + 8*d**3*g*s*vv*z - 4*d**3*g*s*ww*z - 4*d**3*g*s*yy*z + 4*d**3*g*vv*z**2 - 2*d**3*g*ww*z**2 - 2*d**3*g*yy*z**2 - 2*d**3*h*p**2*r + 2*d**3*h*p**2*ww - 4*d**3*h*p*s*vv + 4*d**3*h*p*s*ww - 4*d**3*h*p*vv*z + 4*d**3*h*p*ww*z - 8*d**3*h*s*vv*z + 4*d**3*h*s*ww*z + 4*d**3*h*s*yy*z - 4*d**3*h*vv*z**2 + 2*d**3*h*ww*z**2 + 2*d**3*h*yy*z**2 - 4*d**3*kk*p*q*s - 4*d**3*kk*p*q*z + 4*d**3*kk*p*r*s + 4*d**3*kk*p*r*z - 8*d**3*kk*q*s*z - 4*d**3*kk*q*z**2 + 8*d**3*kk*r*s*z + 4*d**3*kk*r*z**2 + 2*d**3*m*p**2*ww - 4*d**3*m*p*s*vv + 4*d**3*m*p*s*ww - 4*d**3*m*p*vv*z + 4*d**3*m*p*ww*z - 8*d**3*m*s*vv*z + 4*d**3*m*s*ww*z + 4*d**3*m*s*yy*z - 4*d**3*m*vv*z**2 + 2*d**3*m*ww*z**2 + 2*d**3*m*yy*z**2 - 2*d**3*n*p**2*ww + 4*d**3*n*p*s*vv - 4*d**3*n*p*s*ww + 4*d**3*n*p*vv*z - 4*d**3*n*p*ww*z + 8*d**3*n*s*vv*z - 4*d**3*n*s*ww*z - 4*d**3*n*s*yy*z + 4*d**3*n*vv*z**2 - 2*d**3*n*ww*z**2 - 2*d**3*n*yy*z**2 + 2*d**3*p**2*q*xx - 2*d**3*p**2*r*xx + 4*d**3*p*q*s*xx + 4*d**3*p*q*xx*z - 4*d**3*p*r*s*xx - 4*d**3*p*r*xx*z + 4*d**3*q*s*uu*z + 4*d**3*q*s*xx*z + 2*d**3*q*uu*z**2 + 2*d**3*q*xx*z**2 - 4*d**3*r*s*uu*z - 4*d**3*r*s*xx*z - 2*d**3*r*uu*z**2 - 2*d**3*r*xx*z**2 + 2*d**2*f*g*p**2*s + 2*d**2*f*kk*p*s**2 + 4*d**2*f*kk*p*s*z + 4*d**2*f*kk*s**2*z + 4*d**2*f*kk*s*z**2 - 2*d**2*f*p**2*s*xx - 2*d**2*f*p*s**2*xx - 4*d**2*f*p*s*xx*z - 2*d**2*f*s**2*uu*z - 2*d**2*f*s**2*xx*z - 2*d**2*f*s*uu*z**2 - 2*d**2*f*s*xx*z**2 - 12*d**2*g*p**2*q*s + 12*d**2*g*p**2*r*s - 2*d**2*g*p**2*s*ww + 2*d**2*g*p*s**2*vv - 2*d**2*g*p*s**2*ww + 4*d**2*g*p*s*vv*z - 4*d**2*g*p*s*ww*z + 4*d**2*g*s**2*vv*z - 2*d**2*g*s**2*ww*z - 2*d**2*g*s**2*yy*z + 4*d**2*g*s*vv*z**2 - 2*d**2*g*s*ww*z**2 - 2*d**2*g*s*yy*z**2 + 8*d**2*h*p**2*q*s - 12*d**2*h*p**2*r*s + 4*d**2*h*p**2*s*ww - 4*d**2*h*p*s**2*vv + 4*d**2*h*p*s**2*ww - 8*d**2*h*p*s*vv*z + 8*d**2*h*p*s*ww*z - 8*d**2*h*s**2*vv*z + 4*d**2*h*s**2*ww*z + 4*d**2*h*s**2*yy*z - 8*d**2*h*s*vv*z**2 + 4*d**2*h*s*ww*z**2 + 4*d**2*h*s*yy*z**2 - 4*d**2*kk*p*q*s**2 - 8*d**2*kk*p*q*s*z + 2*d**2*kk*p*r*s**2 + 4*d**2*kk*p*r*s*z - 8*d**2*kk*q*s**2*z - 8*d**2*kk*q*s*z**2 + 4*d**2*kk*r*s**2*z + 4*d**2*kk*r*s*z**2 + 2*d**2*l*p**2*r*s - 2*d**2*l*p**2*s*ww + 2*d**2*l*p*s**2*vv - 2*d**2*l*p*s**2*ww + 4*d**2*l*p*s*vv*z - 4*d**2*l*p*s*ww*z + 4*d**2*l*s**2*vv*z - 2*d**2*l*s**2*ww*z - 2*d**2*l*s**2*yy*z + 4*d**2*l*s*vv*z**2 - 2*d**2*l*s*ww*z**2 - 2*d**2*l*s*yy*z**2 + 2*d**2*m*p**2*s*ww - 2*d**2*m*p*s**2*vv + 2*d**2*m*p*s**2*ww - 4*d**2*m*p*s*vv*z + 4*d**2*m*p*s*ww*z - 4*d**2*m*s**2*vv*z + 2*d**2*m*s**2*ww*z + 2*d**2*m*s**2*yy*z - 4*d**2*m*s*vv*z**2 + 2*d**2*m*s*ww*z**2 + 2*d**2*m*s*yy*z**2 - 4*d**2*n*p**2*s*ww + 4*d**2*n*p*s**2*vv - 4*d**2*n*p*s**2*ww + 8*d**2*n*p*s*vv*z - 8*d**2*n*p*s*ww*z + 8*d**2*n*s**2*vv*z - 4*d**2*n*s**2*ww*z - 4*d**2*n*s**2*yy*z + 8*d**2*n*s*vv*z**2 - 4*d**2*n*s*ww*z**2 - 4*d**2*n*s*yy*z**2 + 2*d**2*o*p**2*s*ww - 2*d**2*o*p*s**2*vv + 2*d**2*o*p*s**2*ww - 4*d**2*o*p*s*vv*z + 4*d**2*o*p*s*ww*z - 4*d**2*o*s**2*vv*z + 2*d**2*o*s**2*ww*z + 2*d**2*o*s**2*yy*z - 4*d**2*o*s*vv*z**2 + 2*d**2*o*s*ww*z**2 + 2*d**2*o*s*yy*z**2 + 4*d**2*p**2*q*s*xx - 2*d**2*p**2*r*s*xx + 4*d**2*p*q*s**2*xx + 8*d**2*p*q*s*xx*z - 2*d**2*p*r*s**2*xx - 4*d**2*p*r*s*xx*z + 4*d**2*q*s**2*uu*z + 4*d**2*q*s**2*xx*z + 4*d**2*q*s*uu*z**2 + 4*d**2*q*s*xx*z**2 - 2*d**2*r*s**2*uu*z - 2*d**2*r*s**2*xx*z - 2*d**2*r*s*uu*z**2 - 2*d**2*r*s*xx*z**2 + 6*d*f*g*p**2*s**2 - 6*d*f*h*p**2*s**2 - 18*d*g*p**2*q*s**2 + 12*d*g*p**2*r*s**2 + 24*d*h*p**2*q*s**2 - 18*d*h*p**2*r*s**2 - 6*d*l*p**2*q*s**2 + 6*d*l*p**2*r*s**2 + 4*f*g*p**2*s**3 - 8*f*h*p**2*s**3 + 4*f*l*p**2*s**3 - 8*g*p**2*q*s**3 + 4*g*p**2*r*s**3 + 16*h*p**2*q*s**3 - 8*h*p**2*r*s**3 - 8*l*p**2*q*s**3 + 4*l*p**2*r*s**3) + (-2*a*d**4*k*p - 4*a*d**4*k*z + 2*a*d**4*p*x + 2*a*d**4*u*z + 2*a*d**4*x*z - 4*a*d**3*k*p*s - 4*a*d**3*k*p*z - 8*a*d**3*k*s*z - 4*a*d**3*k*z**2 - 4*a*d**3*m*p**2 + 2*a*d**3*n*p**2 + 2*a*d**3*p**2*x + 4*a*d**3*p*s*x + 4*a*d**3*p*x*z + 4*a*d**3*s*u*z + 4*a*d**3*s*x*z + 2*a*d**3*u*z**2 + 2*a*d**3*x*z**2 - 2*a*d**2*k*p*s**2 - 4*a*d**2*k*p*s*z - 4*a*d**2*k*s**2*z - 4*a*d**2*k*s*z**2 - 12*a*d**2*m*p**2*s + 12*a*d**2*n*p**2*s - 2*a*d**2*o*p**2*s + 2*a*d**2*p**2*s*x + 2*a*d**2*p*s**2*x + 4*a*d**2*p*s*x*z + 2*a*d**2*s**2*u*z + 2*a*d**2*s**2*x*z + 2*a*d**2*s*u*z**2 + 2*a*d**2*s*x*z**2 - 12*a*d*m*p**2*s**2 + 18*a*d*n*p**2*s**2 - 6*a*d*o*p**2*s**2 - 4*a*m*p**2*s**3 + 8*a*n*p**2*s**3 - 4*a*o*p**2*s**3 + 4*b*d**3*k*p*s + 4*b*d**3*k*p*z + 8*b*d**3*k*s*z + 4*b*d**3*k*z**2 + 2*b*d**3*m*p**2 - 2*b*d**3*p**2*x - 4*b*d**3*p*s*x - 4*b*d**3*p*x*z - 4*b*d**3*s*u*z - 4*b*d**3*s*x*z - 2*b*d**3*u*z**2 - 2*b*d**3*x*z**2 + 4*b*d**2*k*p*s**2 + 8*b*d**2*k*p*s*z + 8*b*d**2*k*s**2*z + 8*b*d**2*k*s*z**2 + 12*b*d**2*m*p**2*s - 8*b*d**2*n*p**2*s - 4*b*d**2*p**2*s*x - 4*b*d**2*p*s**2*x - 8*b*d**2*p*s*x*z - 4*b*d**2*s**2*u*z - 4*b*d**2*s**2*x*z - 4*b*d**2*s*u*z**2 - 4*b*d**2*s*x*z**2 + 18*b*d*m*p**2*s**2 - 24*b*d*n*p**2*s**2 + 6*b*d*o*p**2*s**2 + 8*b*m*p**2*s**3 - 16*b*n*p**2*s**3 + 8*b*o*p**2*s**3 - 2*c*d**2*k*p*s**2 - 4*c*d**2*k*p*s*z - 4*c*d**2*k*s**2*z - 4*c*d**2*k*s*z**2 - 2*c*d**2*m*p**2*s + 2*c*d**2*p**2*s*x + 2*c*d**2*p*s**2*x + 4*c*d**2*p*s*x*z + 2*c*d**2*s**2*u*z + 2*c*d**2*s**2*x*z + 2*c*d**2*s*u*z**2 + 2*c*d**2*s*x*z**2 - 6*c*d*m*p**2*s**2 + 6*c*d*n*p**2*s**2 - 4*c*m*p**2*s**3 + 8*c*n*p**2*s**3 - 4*c*o*p**2*s**3 + 2*d**4*g*p*v - 2*d**4*g*p*w + 4*d**4*g*v*z - 2*d**4*g*w*z - 2*d**4*g*y*z + 2*d**4*k*p*r + 4*d**4*k*r*z - 2*d**4*m*p*v + 2*d**4*m*p*w - 4*d**4*m*v*z + 2*d**4*m*w*z + 2*d**4*m*y*z - 2*d**4*p*r*x - 2*d**4*r*u*z - 2*d**4*r*x*z - 2*d**3*g*p**2*q + 4*d**3*g*p**2*r - 2*d**3*g*p**2*w + 4*d**3*g*p*s*v - 4*d**3*g*p*s*w + 4*d**3*g*p*v*z - 4*d**3*g*p*w*z + 8*d**3*g*s*v*z - 4*d**3*g*s*w*z - 4*d**3*g*s*y*z + 4*d**3*g*v*z**2 - 2*d**3*g*w*z**2 - 2*d**3*g*y*z**2 - 2*d**3*h*p**2*r + 2*d**3*h*p**2*w - 4*d**3*h*p*s*v + 4*d**3*h*p*s*w - 4*d**3*h*p*v*z + 4*d**3*h*p*w*z - 8*d**3*h*s*v*z + 4*d**3*h*s*w*z + 4*d**3*h*s*y*z - 4*d**3*h*v*z**2 + 2*d**3*h*w*z**2 + 2*d**3*h*y*z**2 - 4*d**3*k*p*q*s - 4*d**3*k*p*q*z + 4*d**3*k*p*r*s + 4*d**3*k*p*r*z - 8*d**3*k*q*s*z - 4*d**3*k*q*z**2 + 8*d**3*k*r*s*z + 4*d**3*k*r*z**2 + 2*d**3*m*p**2*w - 4*d**3*m*p*s*v + 4*d**3*m*p*s*w - 4*d**3*m*p*v*z + 4*d**3*m*p*w*z - 8*d**3*m*s*v*z + 4*d**3*m*s*w*z + 4*d**3*m*s*y*z - 4*d**3*m*v*z**2 + 2*d**3*m*w*z**2 + 2*d**3*m*y*z**2 - 2*d**3*n*p**2*w + 4*d**3*n*p*s*v - 4*d**3*n*p*s*w + 4*d**3*n*p*v*z - 4*d**3*n*p*w*z + 8*d**3*n*s*v*z - 4*d**3*n*s*w*z - 4*d**3*n*s*y*z + 4*d**3*n*v*z**2 - 2*d**3*n*w*z**2 - 2*d**3*n*y*z**2 + 2*d**3*p**2*q*x - 2*d**3*p**2*r*x + 4*d**3*p*q*s*x + 4*d**3*p*q*x*z - 4*d**3*p*r*s*x - 4*d**3*p*r*x*z + 4*d**3*q*s*u*z + 4*d**3*q*s*x*z + 2*d**3*q*u*z**2 + 2*d**3*q*x*z**2 - 4*d**3*r*s*u*z - 4*d**3*r*s*x*z - 2*d**3*r*u*z**2 - 2*d**3*r*x*z**2 + 2*d**2*f*g*p**2*s + 2*d**2*f*k*p*s**2 + 4*d**2*f*k*p*s*z + 4*d**2*f*k*s**2*z + 4*d**2*f*k*s*z**2 - 2*d**2*f*p**2*s*x - 2*d**2*f*p*s**2*x - 4*d**2*f*p*s*x*z - 2*d**2*f*s**2*u*z - 2*d**2*f*s**2*x*z - 2*d**2*f*s*u*z**2 - 2*d**2*f*s*x*z**2 - 12*d**2*g*p**2*q*s + 12*d**2*g*p**2*r*s - 2*d**2*g*p**2*s*w + 2*d**2*g*p*s**2*v - 2*d**2*g*p*s**2*w + 4*d**2*g*p*s*v*z - 4*d**2*g*p*s*w*z + 4*d**2*g*s**2*v*z - 2*d**2*g*s**2*w*z - 2*d**2*g*s**2*y*z + 4*d**2*g*s*v*z**2 - 2*d**2*g*s*w*z**2 - 2*d**2*g*s*y*z**2 + 8*d**2*h*p**2*q*s - 12*d**2*h*p**2*r*s + 4*d**2*h*p**2*s*w - 4*d**2*h*p*s**2*v + 4*d**2*h*p*s**2*w - 8*d**2*h*p*s*v*z + 8*d**2*h*p*s*w*z - 8*d**2*h*s**2*v*z + 4*d**2*h*s**2*w*z + 4*d**2*h*s**2*y*z - 8*d**2*h*s*v*z**2 + 4*d**2*h*s*w*z**2 + 4*d**2*h*s*y*z**2 - 4*d**2*k*p*q*s**2 - 8*d**2*k*p*q*s*z + 2*d**2*k*p*r*s**2 + 4*d**2*k*p*r*s*z - 8*d**2*k*q*s**2*z - 8*d**2*k*q*s*z**2 + 4*d**2*k*r*s**2*z + 4*d**2*k*r*s*z**2 + 2*d**2*l*p**2*r*s - 2*d**2*l*p**2*s*w + 2*d**2*l*p*s**2*v - 2*d**2*l*p*s**2*w + 4*d**2*l*p*s*v*z - 4*d**2*l*p*s*w*z + 4*d**2*l*s**2*v*z - 2*d**2*l*s**2*w*z - 2*d**2*l*s**2*y*z + 4*d**2*l*s*v*z**2 - 2*d**2*l*s*w*z**2 - 2*d**2*l*s*y*z**2 + 2*d**2*m*p**2*s*w - 2*d**2*m*p*s**2*v + 2*d**2*m*p*s**2*w - 4*d**2*m*p*s*v*z + 4*d**2*m*p*s*w*z - 4*d**2*m*s**2*v*z + 2*d**2*m*s**2*w*z + 2*d**2*m*s**2*y*z - 4*d**2*m*s*v*z**2 + 2*d**2*m*s*w*z**2 + 2*d**2*m*s*y*z**2 - 4*d**2*n*p**2*s*w + 4*d**2*n*p*s**2*v - 4*d**2*n*p*s**2*w + 8*d**2*n*p*s*v*z - 8*d**2*n*p*s*w*z + 8*d**2*n*s**2*v*z - 4*d**2*n*s**2*w*z - 4*d**2*n*s**2*y*z + 8*d**2*n*s*v*z**2 - 4*d**2*n*s*w*z**2 - 4*d**2*n*s*y*z**2 + 2*d**2*o*p**2*s*w - 2*d**2*o*p*s**2*v + 2*d**2*o*p*s**2*w - 4*d**2*o*p*s*v*z + 4*d**2*o*p*s*w*z - 4*d**2*o*s**2*v*z + 2*d**2*o*s**2*w*z + 2*d**2*o*s**2*y*z - 4*d**2*o*s*v*z**2 + 2*d**2*o*s*w*z**2 + 2*d**2*o*s*y*z**2 + 4*d**2*p**2*q*s*x - 2*d**2*p**2*r*s*x + 4*d**2*p*q*s**2*x + 8*d**2*p*q*s*x*z - 2*d**2*p*r*s**2*x - 4*d**2*p*r*s*x*z + 4*d**2*q*s**2*u*z + 4*d**2*q*s**2*x*z + 4*d**2*q*s*u*z**2 + 4*d**2*q*s*x*z**2 - 2*d**2*r*s**2*u*z - 2*d**2*r*s**2*x*z - 2*d**2*r*s*u*z**2 - 2*d**2*r*s*x*z**2 + 6*d*f*g*p**2*s**2 - 6*d*f*h*p**2*s**2 - 18*d*g*p**2*q*s**2 + 12*d*g*p**2*r*s**2 + 24*d*h*p**2*q*s**2 - 18*d*h*p**2*r*s**2 - 6*d*l*p**2*q*s**2 + 6*d*l*p**2*r*s**2 + 4*f*g*p**2*s**3 - 8*f*h*p**2*s**3 + 4*f*l*p**2*s**3 - 8*g*p**2*q*s**3 + 4*g*p**2*r*s**3 + 16*h*p**2*q*s**3 - 8*h*p**2*r*s**3 - 8*l*p**2*q*s**3 + 4*l*p**2*r*s**3)) / (d**4*p**2)
    a2 = ((+2*a*d**4*kk - a*d**4*uu - a*d**4*xx + 4*a*d**3*kk*p + 4*a*d**3*kk*s + 8*a*d**3*kk*z - 4*a*d**3*p*xx - 2*a*d**3*s*uu - 2*a*d**3*s*xx - 4*a*d**3*uu*z - 4*a*d**3*xx*z + 4*a*d**2*kk*p*s + 2*a*d**2*kk*p*z + 2*a*d**2*kk*s**2 + 8*a*d**2*kk*s*z + 2*a*d**2*kk*z**2 + 6*a*d**2*m*p**2 - 6*a*d**2*n*p**2 + a*d**2*o*p**2 - a*d**2*p**2*xx - 4*a*d**2*p*s*xx - 2*a*d**2*p*xx*z - a*d**2*s**2*uu - a*d**2*s**2*xx - 4*a*d**2*s*uu*z - 4*a*d**2*s*xx*z - a*d**2*uu*z**2 - a*d**2*xx*z**2 + 12*a*d*m*p**2*s - 18*a*d*n*p**2*s + 6*a*d*o*p**2*s + 6*a*m*p**2*s**2 - 12*a*n*p**2*s**2 + 6*a*o*p**2*s**2 - 4*b*d**3*kk*p - 4*b*d**3*kk*s - 8*b*d**3*kk*z + 4*b*d**3*p*xx + 2*b*d**3*s*uu + 2*b*d**3*s*xx + 4*b*d**3*uu*z + 4*b*d**3*xx*z - 8*b*d**2*kk*p*s - 4*b*d**2*kk*p*z - 4*b*d**2*kk*s**2 - 16*b*d**2*kk*s*z - 4*b*d**2*kk*z**2 - 6*b*d**2*m*p**2 + 4*b*d**2*n*p**2 + 2*b*d**2*p**2*xx + 8*b*d**2*p*s*xx + 4*b*d**2*p*xx*z + 2*b*d**2*s**2*uu + 2*b*d**2*s**2*xx + 8*b*d**2*s*uu*z + 8*b*d**2*s*xx*z + 2*b*d**2*uu*z**2 + 2*b*d**2*xx*z**2 - 18*b*d*m*p**2*s + 24*b*d*n*p**2*s - 6*b*d*o*p**2*s - 12*b*m*p**2*s**2 + 24*b*n*p**2*s**2 - 12*b*o*p**2*s**2 + 4*c*d**2*kk*p*s + 2*c*d**2*kk*p*z + 2*c*d**2*kk*s**2 + 8*c*d**2*kk*s*z + 2*c*d**2*kk*z**2 + c*d**2*m*p**2 - c*d**2*p**2*xx - 4*c*d**2*p*s*xx - 2*c*d**2*p*xx*z - c*d**2*s**2*uu - c*d**2*s**2*xx - 4*c*d**2*s*uu*z - 4*c*d**2*s*xx*z - c*d**2*uu*z**2 - c*d**2*xx*z**2 + 6*c*d*m*p**2*s - 6*c*d*n*p**2*s + 6*c*m*p**2*s**2 - 12*c*n*p**2*s**2 + 6*c*o*p**2*s**2 - 2*d**4*g*vv + d**4*g*ww + d**4*g*yy - 2*d**4*kk*r + 2*d**4*m*vv - d**4*m*ww - d**4*m*yy + d**4*r*uu + d**4*r*xx - 4*d**3*g*p*vv + 4*d**3*g*p*ww - 4*d**3*g*s*vv + 2*d**3*g*s*ww + 2*d**3*g*s*yy - 8*d**3*g*vv*z + 4*d**3*g*ww*z + 4*d**3*g*yy*z + 4*d**3*h*p*vv - 4*d**3*h*p*ww + 4*d**3*h*s*vv - 2*d**3*h*s*ww - 2*d**3*h*s*yy + 8*d**3*h*vv*z - 4*d**3*h*ww*z - 4*d**3*h*yy*z + 4*d**3*kk*p*q - 4*d**3*kk*p*r + 4*d**3*kk*q*s + 8*d**3*kk*q*z - 4*d**3*kk*r*s - 8*d**3*kk*r*z + 4*d**3*m*p*vv - 4*d**3*m*p*ww + 4*d**3*m*s*vv - 2*d**3*m*s*ww - 2*d**3*m*s*yy + 8*d**3*m*vv*z - 4*d**3*m*ww*z - 4*d**3*m*yy*z - 4*d**3*n*p*vv + 4*d**3*n*p*ww - 4*d**3*n*s*vv + 2*d**3*n*s*ww + 2*d**3*n*s*yy - 8*d**3*n*vv*z + 4*d**3*n*ww*z + 4*d**3*n*yy*z - 4*d**3*p*q*xx + 4*d**3*p*r*xx - 2*d**3*q*s*uu - 2*d**3*q*s*xx - 4*d**3*q*uu*z - 4*d**3*q*xx*z + 2*d**3*r*s*uu + 2*d**3*r*s*xx + 4*d**3*r*uu*z + 4*d**3*r*xx*z - d**2*f*g*p**2 - 4*d**2*f*kk*p*s - 2*d**2*f*kk*p*z - 2*d**2*f*kk*s**2 - 8*d**2*f*kk*s*z - 2*d**2*f*kk*z**2 + d**2*f*p**2*xx + 4*d**2*f*p*s*xx + 2*d**2*f*p*xx*z + d**2*f*s**2*uu + d**2*f*s**2*xx + 4*d**2*f*s*uu*z + 4*d**2*f*s*xx*z + d**2*f*uu*z**2 + d**2*f*xx*z**2 + 6*d**2*g*p**2*q - 6*d**2*g*p**2*r + d**2*g*p**2*ww - 4*d**2*g*p*s*vv + 4*d**2*g*p*s*ww - 2*d**2*g*p*vv*z + 2*d**2*g*p*ww*z - 2*d**2*g*s**2*vv + d**2*g*s**2*ww + d**2*g*s**2*yy - 8*d**2*g*s*vv*z + 4*d**2*g*s*ww*z + 4*d**2*g*s*yy*z - 2*d**2*g*vv*z**2 + d**2*g*ww*z**2 + d**2*g*yy*z**2 - 4*d**2*h*p**2*q + 6*d**2*h*p**2*r - 2*d**2*h*p**2*ww + 8*d**2*h*p*s*vv - 8*d**2*h*p*s*ww + 4*d**2*h*p*vv*z - 4*d**2*h*p*ww*z + 4*d**2*h*s**2*vv - 2*d**2*h*s**2*ww - 2*d**2*h*s**2*yy + 16*d**2*h*s*vv*z - 8*d**2*h*s*ww*z - 8*d**2*h*s*yy*z + 4*d**2*h*vv*z**2 - 2*d**2*h*ww*z**2 - 2*d**2*h*yy*z**2 + 8*d**2*kk*p*q*s + 4*d**2*kk*p*q*z - 4*d**2*kk*p*r*s - 2*d**2*kk*p*r*z + 4*d**2*kk*q*s**2 + 16*d**2*kk*q*s*z + 4*d**2*kk*q*z**2 - 2*d**2*kk*r*s**2 - 8*d**2*kk*r*s*z - 2*d**2*kk*r*z**2 - d**2*l*p**2*r + d**2*l*p**2*ww - 4*d**2*l*p*s*vv + 4*d**2*l*p*s*ww - 2*d**2*l*p*vv*z + 2*d**2*l*p*ww*z - 2*d**2*l*s**2*vv + d**2*l*s**2*ww + d**2*l*s**2*yy - 8*d**2*l*s*vv*z + 4*d**2*l*s*ww*z + 4*d**2*l*s*yy*z - 2*d**2*l*vv*z**2 + d**2*l*ww*z**2 + d**2*l*yy*z**2 - d**2*m*p**2*ww + 4*d**2*m*p*s*vv - 4*d**2*m*p*s*ww + 2*d**2*m*p*vv*z - 2*d**2*m*p*ww*z + 2*d**2*m*s**2*vv - d**2*m*s**2*ww - d**2*m*s**2*yy + 8*d**2*m*s*vv*z - 4*d**2*m*s*ww*z - 4*d**2*m*s*yy*z + 2*d**2*m*vv*z**2 - d**2*m*ww*z**2 - d**2*m*yy*z**2 + 2*d**2*n*p**2*ww - 8*d**2*n*p*s*vv + 8*d**2*n*p*s*ww - 4*d**2*n*p*vv*z + 4*d**2*n*p*ww*z - 4*d**2*n*s**2*vv + 2*d**2*n*s**2*ww + 2*d**2*n*s**2*yy - 16*d**2*n*s*vv*z + 8*d**2*n*s*ww*z + 8*d**2*n*s*yy*z - 4*d**2*n*vv*z**2 + 2*d**2*n*ww*z**2 + 2*d**2*n*yy*z**2 - d**2*o*p**2*ww + 4*d**2*o*p*s*vv - 4*d**2*o*p*s*ww + 2*d**2*o*p*vv*z - 2*d**2*o*p*ww*z + 2*d**2*o*s**2*vv - d**2*o*s**2*ww - d**2*o*s**2*yy + 8*d**2*o*s*vv*z - 4*d**2*o*s*ww*z - 4*d**2*o*s*yy*z + 2*d**2*o*vv*z**2 - d**2*o*ww*z**2 - d**2*o*yy*z**2 - 2*d**2*p**2*q*xx + d**2*p**2*r*xx - 8*d**2*p*q*s*xx - 4*d**2*p*q*xx*z + 4*d**2*p*r*s*xx + 2*d**2*p*r*xx*z - 2*d**2*q*s**2*uu - 2*d**2*q*s**2*xx - 8*d**2*q*s*uu*z - 8*d**2*q*s*xx*z - 2*d**2*q*uu*z**2 - 2*d**2*q*xx*z**2 + d**2*r*s**2*uu + d**2*r*s**2*xx + 4*d**2*r*s*uu*z + 4*d**2*r*s*xx*z + d**2*r*uu*z**2 + d**2*r*xx*z**2 - 6*d*f*g*p**2*s + 6*d*f*h*p**2*s + 18*d*g*p**2*q*s - 12*d*g*p**2*r*s - 24*d*h*p**2*q*s + 18*d*h*p**2*r*s + 6*d*l*p**2*q*s - 6*d*l*p**2*r*s - 6*f*g*p**2*s**2 + 12*f*h*p**2*s**2 - 6*f*l*p**2*s**2 + 12*g*p**2*q*s**2 - 6*g*p**2*r*s**2 - 24*h*p**2*q*s**2 + 12*h*p**2*r*s**2 + 12*l*p**2*q*s**2 - 6*l*p**2*r*s**2) + (+2*a*d**4*k - a*d**4*u - a*d**4*x + 4*a*d**3*k*p + 4*a*d**3*k*s + 8*a*d**3*k*z - 4*a*d**3*p*x - 2*a*d**3*s*u - 2*a*d**3*s*x - 4*a*d**3*u*z - 4*a*d**3*x*z + 4*a*d**2*k*p*s + 2*a*d**2*k*p*z + 2*a*d**2*k*s**2 + 8*a*d**2*k*s*z + 2*a*d**2*k*z**2 + 6*a*d**2*m*p**2 - 6*a*d**2*n*p**2 + a*d**2*o*p**2 - a*d**2*p**2*x - 4*a*d**2*p*s*x - 2*a*d**2*p*x*z - a*d**2*s**2*u - a*d**2*s**2*x - 4*a*d**2*s*u*z - 4*a*d**2*s*x*z - a*d**2*u*z**2 - a*d**2*x*z**2 + 12*a*d*m*p**2*s - 18*a*d*n*p**2*s + 6*a*d*o*p**2*s + 6*a*m*p**2*s**2 - 12*a*n*p**2*s**2 + 6*a*o*p**2*s**2 - 4*b*d**3*k*p - 4*b*d**3*k*s - 8*b*d**3*k*z + 4*b*d**3*p*x + 2*b*d**3*s*u + 2*b*d**3*s*x + 4*b*d**3*u*z + 4*b*d**3*x*z - 8*b*d**2*k*p*s - 4*b*d**2*k*p*z - 4*b*d**2*k*s**2 - 16*b*d**2*k*s*z - 4*b*d**2*k*z**2 - 6*b*d**2*m*p**2 + 4*b*d**2*n*p**2 + 2*b*d**2*p**2*x + 8*b*d**2*p*s*x + 4*b*d**2*p*x*z + 2*b*d**2*s**2*u + 2*b*d**2*s**2*x + 8*b*d**2*s*u*z + 8*b*d**2*s*x*z + 2*b*d**2*u*z**2 + 2*b*d**2*x*z**2 - 18*b*d*m*p**2*s + 24*b*d*n*p**2*s - 6*b*d*o*p**2*s - 12*b*m*p**2*s**2 + 24*b*n*p**2*s**2 - 12*b*o*p**2*s**2 + 4*c*d**2*k*p*s + 2*c*d**2*k*p*z + 2*c*d**2*k*s**2 + 8*c*d**2*k*s*z + 2*c*d**2*k*z**2 + c*d**2*m*p**2 - c*d**2*p**2*x - 4*c*d**2*p*s*x - 2*c*d**2*p*x*z - c*d**2*s**2*u - c*d**2*s**2*x - 4*c*d**2*s*u*z - 4*c*d**2*s*x*z - c*d**2*u*z**2 - c*d**2*x*z**2 + 6*c*d*m*p**2*s - 6*c*d*n*p**2*s + 6*c*m*p**2*s**2 - 12*c*n*p**2*s**2 + 6*c*o*p**2*s**2 - 2*d**4*g*v + d**4*g*w + d**4*g*y - 2*d**4*k*r + 2*d**4*m*v - d**4*m*w - d**4*m*y + d**4*r*u + d**4*r*x - 4*d**3*g*p*v + 4*d**3*g*p*w - 4*d**3*g*s*v + 2*d**3*g*s*w + 2*d**3*g*s*y - 8*d**3*g*v*z + 4*d**3*g*w*z + 4*d**3*g*y*z + 4*d**3*h*p*v - 4*d**3*h*p*w + 4*d**3*h*s*v - 2*d**3*h*s*w - 2*d**3*h*s*y + 8*d**3*h*v*z - 4*d**3*h*w*z - 4*d**3*h*y*z + 4*d**3*k*p*q - 4*d**3*k*p*r + 4*d**3*k*q*s + 8*d**3*k*q*z - 4*d**3*k*r*s - 8*d**3*k*r*z + 4*d**3*m*p*v - 4*d**3*m*p*w + 4*d**3*m*s*v - 2*d**3*m*s*w - 2*d**3*m*s*y + 8*d**3*m*v*z - 4*d**3*m*w*z - 4*d**3*m*y*z - 4*d**3*n*p*v + 4*d**3*n*p*w - 4*d**3*n*s*v + 2*d**3*n*s*w + 2*d**3*n*s*y - 8*d**3*n*v*z + 4*d**3*n*w*z + 4*d**3*n*y*z - 4*d**3*p*q*x + 4*d**3*p*r*x - 2*d**3*q*s*u - 2*d**3*q*s*x - 4*d**3*q*u*z - 4*d**3*q*x*z + 2*d**3*r*s*u + 2*d**3*r*s*x + 4*d**3*r*u*z + 4*d**3*r*x*z - d**2*f*g*p**2 - 4*d**2*f*k*p*s - 2*d**2*f*k*p*z - 2*d**2*f*k*s**2 - 8*d**2*f*k*s*z - 2*d**2*f*k*z**2 + d**2*f*p**2*x + 4*d**2*f*p*s*x + 2*d**2*f*p*x*z + d**2*f*s**2*u + d**2*f*s**2*x + 4*d**2*f*s*u*z + 4*d**2*f*s*x*z + d**2*f*u*z**2 + d**2*f*x*z**2 + 6*d**2*g*p**2*q - 6*d**2*g*p**2*r + d**2*g*p**2*w - 4*d**2*g*p*s*v + 4*d**2*g*p*s*w - 2*d**2*g*p*v*z + 2*d**2*g*p*w*z - 2*d**2*g*s**2*v + d**2*g*s**2*w + d**2*g*s**2*y - 8*d**2*g*s*v*z + 4*d**2*g*s*w*z + 4*d**2*g*s*y*z - 2*d**2*g*v*z**2 + d**2*g*w*z**2 + d**2*g*y*z**2 - 4*d**2*h*p**2*q + 6*d**2*h*p**2*r - 2*d**2*h*p**2*w + 8*d**2*h*p*s*v - 8*d**2*h*p*s*w + 4*d**2*h*p*v*z - 4*d**2*h*p*w*z + 4*d**2*h*s**2*v - 2*d**2*h*s**2*w - 2*d**2*h*s**2*y + 16*d**2*h*s*v*z - 8*d**2*h*s*w*z - 8*d**2*h*s*y*z + 4*d**2*h*v*z**2 - 2*d**2*h*w*z**2 - 2*d**2*h*y*z**2 + 8*d**2*k*p*q*s + 4*d**2*k*p*q*z - 4*d**2*k*p*r*s - 2*d**2*k*p*r*z + 4*d**2*k*q*s**2 + 16*d**2*k*q*s*z + 4*d**2*k*q*z**2 - 2*d**2*k*r*s**2 - 8*d**2*k*r*s*z - 2*d**2*k*r*z**2 - d**2*l*p**2*r + d**2*l*p**2*w - 4*d**2*l*p*s*v + 4*d**2*l*p*s*w - 2*d**2*l*p*v*z + 2*d**2*l*p*w*z - 2*d**2*l*s**2*v + d**2*l*s**2*w + d**2*l*s**2*y - 8*d**2*l*s*v*z + 4*d**2*l*s*w*z + 4*d**2*l*s*y*z - 2*d**2*l*v*z**2 + d**2*l*w*z**2 + d**2*l*y*z**2 - d**2*m*p**2*w + 4*d**2*m*p*s*v - 4*d**2*m*p*s*w + 2*d**2*m*p*v*z - 2*d**2*m*p*w*z + 2*d**2*m*s**2*v - d**2*m*s**2*w - d**2*m*s**2*y + 8*d**2*m*s*v*z - 4*d**2*m*s*w*z - 4*d**2*m*s*y*z + 2*d**2*m*v*z**2 - d**2*m*w*z**2 - d**2*m*y*z**2 + 2*d**2*n*p**2*w - 8*d**2*n*p*s*v + 8*d**2*n*p*s*w - 4*d**2*n*p*v*z + 4*d**2*n*p*w*z - 4*d**2*n*s**2*v + 2*d**2*n*s**2*w + 2*d**2*n*s**2*y - 16*d**2*n*s*v*z + 8*d**2*n*s*w*z + 8*d**2*n*s*y*z - 4*d**2*n*v*z**2 + 2*d**2*n*w*z**2 + 2*d**2*n*y*z**2 - d**2*o*p**2*w + 4*d**2*o*p*s*v - 4*d**2*o*p*s*w + 2*d**2*o*p*v*z - 2*d**2*o*p*w*z + 2*d**2*o*s**2*v - d**2*o*s**2*w - d**2*o*s**2*y + 8*d**2*o*s*v*z - 4*d**2*o*s*w*z - 4*d**2*o*s*y*z + 2*d**2*o*v*z**2 - d**2*o*w*z**2 - d**2*o*y*z**2 - 2*d**2*p**2*q*x + d**2*p**2*r*x - 8*d**2*p*q*s*x - 4*d**2*p*q*x*z + 4*d**2*p*r*s*x + 2*d**2*p*r*x*z - 2*d**2*q*s**2*u - 2*d**2*q*s**2*x - 8*d**2*q*s*u*z - 8*d**2*q*s*x*z - 2*d**2*q*u*z**2 - 2*d**2*q*x*z**2 + d**2*r*s**2*u + d**2*r*s**2*x + 4*d**2*r*s*u*z + 4*d**2*r*s*x*z + d**2*r*u*z**2 + d**2*r*x*z**2 - 6*d*f*g*p**2*s + 6*d*f*h*p**2*s + 18*d*g*p**2*q*s - 12*d*g*p**2*r*s - 24*d*h*p**2*q*s + 18*d*h*p**2*r*s + 6*d*l*p**2*q*s - 6*d*l*p**2*r*s - 6*f*g*p**2*s**2 + 12*f*h*p**2*s**2 - 6*f*l*p**2*s**2 + 12*g*p**2*q*s**2 - 6*g*p**2*r*s**2 - 24*h*p**2*q*s**2 + 12*h*p**2*r*s**2 + 12*l*p**2*q*s**2 - 6*l*p**2*r*s**2)) / (d**4*p**2)
    a3 = ((-4*a*d**3*kk + 2*a*d**3*uu + 2*a*d**3*xx - 2*a*d**2*kk*p - 4*a*d**2*kk*s - 4*a*d**2*kk*z + 2*a*d**2*p*xx + 2*a*d**2*s*uu + 2*a*d**2*s*xx + 2*a*d**2*uu*z + 2*a*d**2*xx*z - 4*a*d*m*p**2 + 6*a*d*n*p**2 - 2*a*d*o*p**2 - 4*a*m*p**2*s + 8*a*n*p**2*s - 4*a*o*p**2*s + 4*b*d**3*kk - 2*b*d**3*uu - 2*b*d**3*xx + 4*b*d**2*kk*p + 8*b*d**2*kk*s + 8*b*d**2*kk*z - 4*b*d**2*p*xx - 4*b*d**2*s*uu - 4*b*d**2*s*xx - 4*b*d**2*uu*z - 4*b*d**2*xx*z + 6*b*d*m*p**2 - 8*b*d*n*p**2 + 2*b*d*o*p**2 + 8*b*m*p**2*s - 16*b*n*p**2*s + 8*b*o*p**2*s - 2*c*d**2*kk*p - 4*c*d**2*kk*s - 4*c*d**2*kk*z + 2*c*d**2*p*xx + 2*c*d**2*s*uu + 2*c*d**2*s*xx + 2*c*d**2*uu*z + 2*c*d**2*xx*z - 2*c*d*m*p**2 + 2*c*d*n*p**2 - 4*c*m*p**2*s + 8*c*n*p**2*s - 4*c*o*p**2*s + 4*d**3*g*vv - 2*d**3*g*ww - 2*d**3*g*yy - 4*d**3*h*vv + 2*d**3*h*ww + 2*d**3*h*yy - 4*d**3*kk*q + 4*d**3*kk*r - 4*d**3*m*vv + 2*d**3*m*ww + 2*d**3*m*yy + 4*d**3*n*vv - 2*d**3*n*ww - 2*d**3*n*yy + 2*d**3*q*uu + 2*d**3*q*xx - 2*d**3*r*uu - 2*d**3*r*xx + 2*d**2*f*kk*p + 4*d**2*f*kk*s + 4*d**2*f*kk*z - 2*d**2*f*p*xx - 2*d**2*f*s*uu - 2*d**2*f*s*xx - 2*d**2*f*uu*z - 2*d**2*f*xx*z + 2*d**2*g*p*vv - 2*d**2*g*p*ww + 4*d**2*g*s*vv - 2*d**2*g*s*ww - 2*d**2*g*s*yy + 4*d**2*g*vv*z - 2*d**2*g*ww*z - 2*d**2*g*yy*z - 4*d**2*h*p*vv + 4*d**2*h*p*ww - 8*d**2*h*s*vv + 4*d**2*h*s*ww + 4*d**2*h*s*yy - 8*d**2*h*vv*z + 4*d**2*h*ww*z + 4*d**2*h*yy*z - 4*d**2*kk*p*q + 2*d**2*kk*p*r - 8*d**2*kk*q*s - 8*d**2*kk*q*z + 4*d**2*kk*r*s + 4*d**2*kk*r*z + 2*d**2*l*p*vv - 2*d**2*l*p*ww + 4*d**2*l*s*vv - 2*d**2*l*s*ww - 2*d**2*l*s*yy + 4*d**2*l*vv*z - 2*d**2*l*ww*z - 2*d**2*l*yy*z - 2*d**2*m*p*vv + 2*d**2*m*p*ww - 4*d**2*m*s*vv + 2*d**2*m*s*ww + 2*d**2*m*s*yy - 4*d**2*m*vv*z + 2*d**2*m*ww*z + 2*d**2*m*yy*z + 4*d**2*n*p*vv - 4*d**2*n*p*ww + 8*d**2*n*s*vv - 4*d**2*n*s*ww - 4*d**2*n*s*yy + 8*d**2*n*vv*z - 4*d**2*n*ww*z - 4*d**2*n*yy*z - 2*d**2*o*p*vv + 2*d**2*o*p*ww - 4*d**2*o*s*vv + 2*d**2*o*s*ww + 2*d**2*o*s*yy - 4*d**2*o*vv*z + 2*d**2*o*ww*z + 2*d**2*o*yy*z + 4*d**2*p*q*xx - 2*d**2*p*r*xx + 4*d**2*q*s*uu + 4*d**2*q*s*xx + 4*d**2*q*uu*z + 4*d**2*q*xx*z - 2*d**2*r*s*uu - 2*d**2*r*s*xx - 2*d**2*r*uu*z - 2*d**2*r*xx*z + 2*d*f*g*p**2 - 2*d*f*h*p**2 - 6*d*g*p**2*q + 4*d*g*p**2*r + 8*d*h*p**2*q - 6*d*h*p**2*r - 2*d*l*p**2*q + 2*d*l*p**2*r + 4*f*g*p**2*s - 8*f*h*p**2*s + 4*f*l*p**2*s - 8*g*p**2*q*s + 4*g*p**2*r*s + 16*h*p**2*q*s - 8*h*p**2*r*s - 8*l*p**2*q*s + 4*l*p**2*r*s) + (-4*a*d**3*k + 2*a*d**3*u + 2*a*d**3*x - 2*a*d**2*k*p - 4*a*d**2*k*s - 4*a*d**2*k*z + 2*a*d**2*p*x + 2*a*d**2*s*u + 2*a*d**2*s*x + 2*a*d**2*u*z + 2*a*d**2*x*z - 4*a*d*m*p**2 + 6*a*d*n*p**2 - 2*a*d*o*p**2 - 4*a*m*p**2*s + 8*a*n*p**2*s - 4*a*o*p**2*s + 4*b*d**3*k - 2*b*d**3*u - 2*b*d**3*x + 4*b*d**2*k*p + 8*b*d**2*k*s + 8*b*d**2*k*z - 4*b*d**2*p*x - 4*b*d**2*s*u - 4*b*d**2*s*x - 4*b*d**2*u*z - 4*b*d**2*x*z + 6*b*d*m*p**2 - 8*b*d*n*p**2 + 2*b*d*o*p**2 + 8*b*m*p**2*s - 16*b*n*p**2*s + 8*b*o*p**2*s - 2*c*d**2*k*p - 4*c*d**2*k*s - 4*c*d**2*k*z + 2*c*d**2*p*x + 2*c*d**2*s*u + 2*c*d**2*s*x + 2*c*d**2*u*z + 2*c*d**2*x*z - 2*c*d*m*p**2 + 2*c*d*n*p**2 - 4*c*m*p**2*s + 8*c*n*p**2*s - 4*c*o*p**2*s + 4*d**3*g*v - 2*d**3*g*w - 2*d**3*g*y - 4*d**3*h*v + 2*d**3*h*w + 2*d**3*h*y - 4*d**3*k*q + 4*d**3*k*r - 4*d**3*m*v + 2*d**3*m*w + 2*d**3*m*y + 4*d**3*n*v - 2*d**3*n*w - 2*d**3*n*y + 2*d**3*q*u + 2*d**3*q*x - 2*d**3*r*u - 2*d**3*r*x + 2*d**2*f*k*p + 4*d**2*f*k*s + 4*d**2*f*k*z - 2*d**2*f*p*x - 2*d**2*f*s*u - 2*d**2*f*s*x - 2*d**2*f*u*z - 2*d**2*f*x*z + 2*d**2*g*p*v - 2*d**2*g*p*w + 4*d**2*g*s*v - 2*d**2*g*s*w - 2*d**2*g*s*y + 4*d**2*g*v*z - 2*d**2*g*w*z - 2*d**2*g*y*z - 4*d**2*h*p*v + 4*d**2*h*p*w - 8*d**2*h*s*v + 4*d**2*h*s*w + 4*d**2*h*s*y - 8*d**2*h*v*z + 4*d**2*h*w*z + 4*d**2*h*y*z - 4*d**2*k*p*q + 2*d**2*k*p*r - 8*d**2*k*q*s - 8*d**2*k*q*z + 4*d**2*k*r*s + 4*d**2*k*r*z + 2*d**2*l*p*v - 2*d**2*l*p*w + 4*d**2*l*s*v - 2*d**2*l*s*w - 2*d**2*l*s*y + 4*d**2*l*v*z - 2*d**2*l*w*z - 2*d**2*l*y*z - 2*d**2*m*p*v + 2*d**2*m*p*w - 4*d**2*m*s*v + 2*d**2*m*s*w + 2*d**2*m*s*y - 4*d**2*m*v*z + 2*d**2*m*w*z + 2*d**2*m*y*z + 4*d**2*n*p*v - 4*d**2*n*p*w + 8*d**2*n*s*v - 4*d**2*n*s*w - 4*d**2*n*s*y + 8*d**2*n*v*z - 4*d**2*n*w*z - 4*d**2*n*y*z - 2*d**2*o*p*v + 2*d**2*o*p*w - 4*d**2*o*s*v + 2*d**2*o*s*w + 2*d**2*o*s*y - 4*d**2*o*v*z + 2*d**2*o*w*z + 2*d**2*o*y*z + 4*d**2*p*q*x - 2*d**2*p*r*x + 4*d**2*q*s*u + 4*d**2*q*s*x + 4*d**2*q*u*z + 4*d**2*q*x*z - 2*d**2*r*s*u - 2*d**2*r*s*x - 2*d**2*r*u*z - 2*d**2*r*x*z + 2*d*f*g*p**2 - 2*d*f*h*p**2 - 6*d*g*p**2*q + 4*d*g*p**2*r + 8*d*h*p**2*q - 6*d*h*p**2*r - 2*d*l*p**2*q + 2*d*l*p**2*r + 4*f*g*p**2*s - 8*f*h*p**2*s + 4*f*l*p**2*s - 8*g*p**2*q*s + 4*g*p**2*r*s + 16*h*p**2*q*s - 8*h*p**2*r*s - 8*l*p**2*q*s + 4*l*p**2*r*s)) / (d**4*p**2)
    a4 = ((+2*a*d**2*kk - a*d**2*uu - a*d**2*xx + a*m*p**2 - 2*a*n*p**2 + a*o*p**2 - 4*b*d**2*kk + 2*b*d**2*uu + 2*b*d**2*xx - 2*b*m*p**2 + 4*b*n*p**2 - 2*b*o*p**2 + 2*c*d**2*kk - c*d**2*uu - c*d**2*xx + c*m*p**2 - 2*c*n*p**2 + c*o*p**2 - 2*d**2*f*kk + d**2*f*uu + d**2*f*xx - 2*d**2*g*vv + d**2*g*ww + d**2*g*yy + 4*d**2*h*vv - 2*d**2*h*ww - 2*d**2*h*yy + 4*d**2*kk*q - 2*d**2*kk*r - 2*d**2*l*vv + d**2*l*ww + d**2*l*yy + 2*d**2*m*vv - d**2*m*ww - d**2*m*yy - 4*d**2*n*vv + 2*d**2*n*ww + 2*d**2*n*yy + 2*d**2*o*vv - d**2*o*ww - d**2*o*yy - 2*d**2*q*uu - 2*d**2*q*xx + d**2*r*uu + d**2*r*xx - f*g*p**2 + 2*f*h*p**2 - f*l*p**2 + 2*g*p**2*q - g*p**2*r - 4*h*p**2*q + 2*h*p**2*r + 2*l*p**2*q - l*p**2*r) + (+2*a*d**2*k - a*d**2*u - a*d**2*x + a*m*p**2 - 2*a*n*p**2 + a*o*p**2 - 4*b*d**2*k + 2*b*d**2*u + 2*b*d**2*x - 2*b*m*p**2 + 4*b*n*p**2 - 2*b*o*p**2 + 2*c*d**2*k - c*d**2*u - c*d**2*x + c*m*p**2 - 2*c*n*p**2 + c*o*p**2 - 2*d**2*f*k + d**2*f*u + d**2*f*x - 2*d**2*g*v + d**2*g*w + d**2*g*y + 4*d**2*h*v - 2*d**2*h*w - 2*d**2*h*y + 4*d**2*k*q - 2*d**2*k*r - 2*d**2*l*v + d**2*l*w + d**2*l*y + 2*d**2*m*v - d**2*m*w - d**2*m*y - 4*d**2*n*v + 2*d**2*n*w + 2*d**2*n*y + 2*d**2*o*v - d**2*o*w - d**2*o*y - 2*d**2*q*u - 2*d**2*q*x + d**2*r*u + d**2*r*x - f*g*p**2 + 2*f*h*p**2 - f*l*p**2 + 2*g*p**2*q - g*p**2*r - 4*h*p**2*q + 2*h*p**2*r + 2*l*p**2*q - l*p**2*r)) / (d**4*p**2)
    """

    """
    a0 = (+2*a*d**4*k*p*z + 2*a*d**4*k*z**2 + a*d**4*m*p**2 - a*d**4*p**2*x - 2*a*d**4*p*x*z - a*d**4*u*z**2 - a*d**4*x*z**2 + 4*a*d**3*k*p*s*z + 4*a*d**3*k*s*z**2 + 4*a*d**3*m*p**2*s - 2*a*d**3*n*p**2*s - 2*a*d**3*p**2*s*x - 4*a*d**3*p*s*x*z - 2*a*d**3*s*u*z**2 - 2*a*d**3*s*x*z**2 + 2*a*d**2*k*p*s**2*z + 2*a*d**2*k*s**2*z**2 + 6*a*d**2*m*p**2*s**2 - 6*a*d**2*n*p**2*s**2 + a*d**2*o*p**2*s**2 - a*d**2*p**2*s**2*x - 2*a*d**2*p*s**2*x*z - a*d**2*s**2*u*z**2 - a*d**2*s**2*x*z**2 + 4*a*d*m*p**2*s**3 - 6*a*d*n*p**2*s**3 + 2*a*d*o*p**2*s**3 + a*m*p**2*s**4 - 2*a*n*p**2*s**4 + a*o*p**2*s**4 - 4*b*d**3*k*p*s*z - 4*b*d**3*k*s*z**2 - 2*b*d**3*m*p**2*s + 2*b*d**3*p**2*s*x + 4*b*d**3*p*s*x*z + 2*b*d**3*s*u*z**2 + 2*b*d**3*s*x*z**2 - 4*b*d**2*k*p*s**2*z - 4*b*d**2*k*s**2*z**2 - 6*b*d**2*m*p**2*s**2 + 4*b*d**2*n*p**2*s**2 + 2*b*d**2*p**2*s**2*x + 4*b*d**2*p*s**2*x*z + 2*b*d**2*s**2*u*z**2 + 2*b*d**2*s**2*x*z**2 - 6*b*d*m*p**2*s**3 + 8*b*d*n*p**2*s**3 - 2*b*d*o*p**2*s**3 - 2*b*m*p**2*s**4 + 4*b*n*p**2*s**4 - 2*b*o*p**2*s**4 + 2*c*d**2*k*p*s**2*z + 2*c*d**2*k*s**2*z**2 + c*d**2*m*p**2*s**2 - c*d**2*p**2*s**2*x - 2*c*d**2*p*s**2*x*z - c*d**2*s**2*u*z**2 - c*d**2*s**2*x*z**2 + 2*c*d*m*p**2*s**3 - 2*c*d*n*p**2*s**3 + c*m*p**2*s**4 - 2*c*n*p**2*s**4 + c*o*p**2*s**4 - d**4*g*p**2*r + d**4*g*p**2*w - 2*d**4*g*p*v*z + 2*d**4*g*p*w*z - 2*d**4*g*v*z**2 + d**4*g*w*z**2 + d**4*g*y*z**2 - 2*d**4*k*p*r*z - 2*d**4*k*r*z**2 - d**4*m*p**2*w + 2*d**4*m*p*v*z - 2*d**4*m*p*w*z + 2*d**4*m*v*z**2 - d**4*m*w*z**2 - d**4*m*y*z**2 + d**4*p**2*r*x + 2*d**4*p*r*x*z + d**4*r*u*z**2 + d**4*r*x*z**2 + 2*d**3*g*p**2*q*s - 4*d**3*g*p**2*r*s + 2*d**3*g*p**2*s*w - 4*d**3*g*p*s*v*z + 4*d**3*g*p*s*w*z - 4*d**3*g*s*v*z**2 + 2*d**3*g*s*w*z**2 + 2*d**3*g*s*y*z**2 + 2*d**3*h*p**2*r*s - 2*d**3*h*p**2*s*w + 4*d**3*h*p*s*v*z - 4*d**3*h*p*s*w*z + 4*d**3*h*s*v*z**2 - 2*d**3*h*s*w*z**2 - 2*d**3*h*s*y*z**2 + 4*d**3*k*p*q*s*z - 4*d**3*k*p*r*s*z + 4*d**3*k*q*s*z**2 - 4*d**3*k*r*s*z**2 - 2*d**3*m*p**2*s*w + 4*d**3*m*p*s*v*z - 4*d**3*m*p*s*w*z + 4*d**3*m*s*v*z**2 - 2*d**3*m*s*w*z**2 - 2*d**3*m*s*y*z**2 + 2*d**3*n*p**2*s*w - 4*d**3*n*p*s*v*z + 4*d**3*n*p*s*w*z - 4*d**3*n*s*v*z**2 + 2*d**3*n*s*w*z**2 + 2*d**3*n*s*y*z**2 - 2*d**3*p**2*q*s*x + 2*d**3*p**2*r*s*x - 4*d**3*p*q*s*x*z + 4*d**3*p*r*s*x*z - 2*d**3*q*s*u*z**2 - 2*d**3*q*s*x*z**2 + 2*d**3*r*s*u*z**2 + 2*d**3*r*s*x*z**2 - d**2*f*g*p**2*s**2 - 2*d**2*f*k*p*s**2*z - 2*d**2*f*k*s**2*z**2 + d**2*f*p**2*s**2*x + 2*d**2*f*p*s**2*x*z + d**2*f*s**2*u*z**2 + d**2*f*s**2*x*z**2 + 6*d**2*g*p**2*q*s**2 - 6*d**2*g*p**2*r*s**2 + d**2*g*p**2*s**2*w - 2*d**2*g*p*s**2*v*z + 2*d**2*g*p*s**2*w*z - 2*d**2*g*s**2*v*z**2 + d**2*g*s**2*w*z**2 + d**2*g*s**2*y*z**2 - 4*d**2*h*p**2*q*s**2 + 6*d**2*h*p**2*r*s**2 - 2*d**2*h*p**2*s**2*w + 4*d**2*h*p*s**2*v*z - 4*d**2*h*p*s**2*w*z + 4*d**2*h*s**2*v*z**2 - 2*d**2*h*s**2*w*z**2 - 2*d**2*h*s**2*y*z**2 + 4*d**2*k*p*q*s**2*z - 2*d**2*k*p*r*s**2*z + 4*d**2*k*q*s**2*z**2 - 2*d**2*k*r*s**2*z**2 - d**2*l*p**2*r*s**2 + d**2*l*p**2*s**2*w - 2*d**2*l*p*s**2*v*z + 2*d**2*l*p*s**2*w*z - 2*d**2*l*s**2*v*z**2 + d**2*l*s**2*w*z**2 + d**2*l*s**2*y*z**2 - d**2*m*p**2*s**2*w + 2*d**2*m*p*s**2*v*z - 2*d**2*m*p*s**2*w*z + 2*d**2*m*s**2*v*z**2 - d**2*m*s**2*w*z**2 - d**2*m*s**2*y*z**2 + 2*d**2*n*p**2*s**2*w - 4*d**2*n*p*s**2*v*z + 4*d**2*n*p*s**2*w*z - 4*d**2*n*s**2*v*z**2 + 2*d**2*n*s**2*w*z**2 + 2*d**2*n*s**2*y*z**2 - d**2*o*p**2*s**2*w + 2*d**2*o*p*s**2*v*z - 2*d**2*o*p*s**2*w*z + 2*d**2*o*s**2*v*z**2 - d**2*o*s**2*w*z**2 - d**2*o*s**2*y*z**2 - 2*d**2*p**2*q*s**2*x + d**2*p**2*r*s**2*x - 4*d**2*p*q*s**2*x*z + 2*d**2*p*r*s**2*x*z - 2*d**2*q*s**2*u*z**2 - 2*d**2*q*s**2*x*z**2 + d**2*r*s**2*u*z**2 + d**2*r*s**2*x*z**2 - 2*d*f*g*p**2*s**3 + 2*d*f*h*p**2*s**3 + 6*d*g*p**2*q*s**3 - 4*d*g*p**2*r*s**3 - 8*d*h*p**2*q*s**3 + 6*d*h*p**2*r*s**3 + 2*d*l*p**2*q*s**3 - 2*d*l*p**2*r*s**3 - f*g*p**2*s**4 + 2*f*h*p**2*s**4 - f*l*p**2*s**4 + 2*g*p**2*q*s**4 - g*p**2*r*s**4 - 4*h*p**2*q*s**4 + 2*h*p**2*r*s**4 + 2*l*p**2*q*s**4 - l*p**2*r*s**4) / (d**4*p**2)
    a1 = (-2*a*d**4*k*p - 4*a*d**4*k*z + 2*a*d**4*p*x + 2*a*d**4*u*z + 2*a*d**4*x*z - 4*a*d**3*k*p*s - 4*a*d**3*k*p*z - 8*a*d**3*k*s*z - 4*a*d**3*k*z**2 - 4*a*d**3*m*p**2 + 2*a*d**3*n*p**2 + 2*a*d**3*p**2*x + 4*a*d**3*p*s*x + 4*a*d**3*p*x*z + 4*a*d**3*s*u*z + 4*a*d**3*s*x*z + 2*a*d**3*u*z**2 + 2*a*d**3*x*z**2 - 2*a*d**2*k*p*s**2 - 4*a*d**2*k*p*s*z - 4*a*d**2*k*s**2*z - 4*a*d**2*k*s*z**2 - 12*a*d**2*m*p**2*s + 12*a*d**2*n*p**2*s - 2*a*d**2*o*p**2*s + 2*a*d**2*p**2*s*x + 2*a*d**2*p*s**2*x + 4*a*d**2*p*s*x*z + 2*a*d**2*s**2*u*z + 2*a*d**2*s**2*x*z + 2*a*d**2*s*u*z**2 + 2*a*d**2*s*x*z**2 - 12*a*d*m*p**2*s**2 + 18*a*d*n*p**2*s**2 - 6*a*d*o*p**2*s**2 - 4*a*m*p**2*s**3 + 8*a*n*p**2*s**3 - 4*a*o*p**2*s**3 + 4*b*d**3*k*p*s + 4*b*d**3*k*p*z + 8*b*d**3*k*s*z + 4*b*d**3*k*z**2 + 2*b*d**3*m*p**2 - 2*b*d**3*p**2*x - 4*b*d**3*p*s*x - 4*b*d**3*p*x*z - 4*b*d**3*s*u*z - 4*b*d**3*s*x*z - 2*b*d**3*u*z**2 - 2*b*d**3*x*z**2 + 4*b*d**2*k*p*s**2 + 8*b*d**2*k*p*s*z + 8*b*d**2*k*s**2*z + 8*b*d**2*k*s*z**2 + 12*b*d**2*m*p**2*s - 8*b*d**2*n*p**2*s - 4*b*d**2*p**2*s*x - 4*b*d**2*p*s**2*x - 8*b*d**2*p*s*x*z - 4*b*d**2*s**2*u*z - 4*b*d**2*s**2*x*z - 4*b*d**2*s*u*z**2 - 4*b*d**2*s*x*z**2 + 18*b*d*m*p**2*s**2 - 24*b*d*n*p**2*s**2 + 6*b*d*o*p**2*s**2 + 8*b*m*p**2*s**3 - 16*b*n*p**2*s**3 + 8*b*o*p**2*s**3 - 2*c*d**2*k*p*s**2 - 4*c*d**2*k*p*s*z - 4*c*d**2*k*s**2*z - 4*c*d**2*k*s*z**2 - 2*c*d**2*m*p**2*s + 2*c*d**2*p**2*s*x + 2*c*d**2*p*s**2*x + 4*c*d**2*p*s*x*z + 2*c*d**2*s**2*u*z + 2*c*d**2*s**2*x*z + 2*c*d**2*s*u*z**2 + 2*c*d**2*s*x*z**2 - 6*c*d*m*p**2*s**2 + 6*c*d*n*p**2*s**2 - 4*c*m*p**2*s**3 + 8*c*n*p**2*s**3 - 4*c*o*p**2*s**3 + 2*d**4*g*p*v - 2*d**4*g*p*w + 4*d**4*g*v*z - 2*d**4*g*w*z - 2*d**4*g*y*z + 2*d**4*k*p*r + 4*d**4*k*r*z - 2*d**4*m*p*v + 2*d**4*m*p*w - 4*d**4*m*v*z + 2*d**4*m*w*z + 2*d**4*m*y*z - 2*d**4*p*r*x - 2*d**4*r*u*z - 2*d**4*r*x*z - 2*d**3*g*p**2*q + 4*d**3*g*p**2*r - 2*d**3*g*p**2*w + 4*d**3*g*p*s*v - 4*d**3*g*p*s*w + 4*d**3*g*p*v*z - 4*d**3*g*p*w*z + 8*d**3*g*s*v*z - 4*d**3*g*s*w*z - 4*d**3*g*s*y*z + 4*d**3*g*v*z**2 - 2*d**3*g*w*z**2 - 2*d**3*g*y*z**2 - 2*d**3*h*p**2*r + 2*d**3*h*p**2*w - 4*d**3*h*p*s*v + 4*d**3*h*p*s*w - 4*d**3*h*p*v*z + 4*d**3*h*p*w*z - 8*d**3*h*s*v*z + 4*d**3*h*s*w*z + 4*d**3*h*s*y*z - 4*d**3*h*v*z**2 + 2*d**3*h*w*z**2 + 2*d**3*h*y*z**2 - 4*d**3*k*p*q*s - 4*d**3*k*p*q*z + 4*d**3*k*p*r*s + 4*d**3*k*p*r*z - 8*d**3*k*q*s*z - 4*d**3*k*q*z**2 + 8*d**3*k*r*s*z + 4*d**3*k*r*z**2 + 2*d**3*m*p**2*w - 4*d**3*m*p*s*v + 4*d**3*m*p*s*w - 4*d**3*m*p*v*z + 4*d**3*m*p*w*z - 8*d**3*m*s*v*z + 4*d**3*m*s*w*z + 4*d**3*m*s*y*z - 4*d**3*m*v*z**2 + 2*d**3*m*w*z**2 + 2*d**3*m*y*z**2 - 2*d**3*n*p**2*w + 4*d**3*n*p*s*v - 4*d**3*n*p*s*w + 4*d**3*n*p*v*z - 4*d**3*n*p*w*z + 8*d**3*n*s*v*z - 4*d**3*n*s*w*z - 4*d**3*n*s*y*z + 4*d**3*n*v*z**2 - 2*d**3*n*w*z**2 - 2*d**3*n*y*z**2 + 2*d**3*p**2*q*x - 2*d**3*p**2*r*x + 4*d**3*p*q*s*x + 4*d**3*p*q*x*z - 4*d**3*p*r*s*x - 4*d**3*p*r*x*z + 4*d**3*q*s*u*z + 4*d**3*q*s*x*z + 2*d**3*q*u*z**2 + 2*d**3*q*x*z**2 - 4*d**3*r*s*u*z - 4*d**3*r*s*x*z - 2*d**3*r*u*z**2 - 2*d**3*r*x*z**2 + 2*d**2*f*g*p**2*s + 2*d**2*f*k*p*s**2 + 4*d**2*f*k*p*s*z + 4*d**2*f*k*s**2*z + 4*d**2*f*k*s*z**2 - 2*d**2*f*p**2*s*x - 2*d**2*f*p*s**2*x - 4*d**2*f*p*s*x*z - 2*d**2*f*s**2*u*z - 2*d**2*f*s**2*x*z - 2*d**2*f*s*u*z**2 - 2*d**2*f*s*x*z**2 - 12*d**2*g*p**2*q*s + 12*d**2*g*p**2*r*s - 2*d**2*g*p**2*s*w + 2*d**2*g*p*s**2*v - 2*d**2*g*p*s**2*w + 4*d**2*g*p*s*v*z - 4*d**2*g*p*s*w*z + 4*d**2*g*s**2*v*z - 2*d**2*g*s**2*w*z - 2*d**2*g*s**2*y*z + 4*d**2*g*s*v*z**2 - 2*d**2*g*s*w*z**2 - 2*d**2*g*s*y*z**2 + 8*d**2*h*p**2*q*s - 12*d**2*h*p**2*r*s + 4*d**2*h*p**2*s*w - 4*d**2*h*p*s**2*v + 4*d**2*h*p*s**2*w - 8*d**2*h*p*s*v*z + 8*d**2*h*p*s*w*z - 8*d**2*h*s**2*v*z + 4*d**2*h*s**2*w*z + 4*d**2*h*s**2*y*z - 8*d**2*h*s*v*z**2 + 4*d**2*h*s*w*z**2 + 4*d**2*h*s*y*z**2 - 4*d**2*k*p*q*s**2 - 8*d**2*k*p*q*s*z + 2*d**2*k*p*r*s**2 + 4*d**2*k*p*r*s*z - 8*d**2*k*q*s**2*z - 8*d**2*k*q*s*z**2 + 4*d**2*k*r*s**2*z + 4*d**2*k*r*s*z**2 + 2*d**2*l*p**2*r*s - 2*d**2*l*p**2*s*w + 2*d**2*l*p*s**2*v - 2*d**2*l*p*s**2*w + 4*d**2*l*p*s*v*z - 4*d**2*l*p*s*w*z + 4*d**2*l*s**2*v*z - 2*d**2*l*s**2*w*z - 2*d**2*l*s**2*y*z + 4*d**2*l*s*v*z**2 - 2*d**2*l*s*w*z**2 - 2*d**2*l*s*y*z**2 + 2*d**2*m*p**2*s*w - 2*d**2*m*p*s**2*v + 2*d**2*m*p*s**2*w - 4*d**2*m*p*s*v*z + 4*d**2*m*p*s*w*z - 4*d**2*m*s**2*v*z + 2*d**2*m*s**2*w*z + 2*d**2*m*s**2*y*z - 4*d**2*m*s*v*z**2 + 2*d**2*m*s*w*z**2 + 2*d**2*m*s*y*z**2 - 4*d**2*n*p**2*s*w + 4*d**2*n*p*s**2*v - 4*d**2*n*p*s**2*w + 8*d**2*n*p*s*v*z - 8*d**2*n*p*s*w*z + 8*d**2*n*s**2*v*z - 4*d**2*n*s**2*w*z - 4*d**2*n*s**2*y*z + 8*d**2*n*s*v*z**2 - 4*d**2*n*s*w*z**2 - 4*d**2*n*s*y*z**2 + 2*d**2*o*p**2*s*w - 2*d**2*o*p*s**2*v + 2*d**2*o*p*s**2*w - 4*d**2*o*p*s*v*z + 4*d**2*o*p*s*w*z - 4*d**2*o*s**2*v*z + 2*d**2*o*s**2*w*z + 2*d**2*o*s**2*y*z - 4*d**2*o*s*v*z**2 + 2*d**2*o*s*w*z**2 + 2*d**2*o*s*y*z**2 + 4*d**2*p**2*q*s*x - 2*d**2*p**2*r*s*x + 4*d**2*p*q*s**2*x + 8*d**2*p*q*s*x*z - 2*d**2*p*r*s**2*x - 4*d**2*p*r*s*x*z + 4*d**2*q*s**2*u*z + 4*d**2*q*s**2*x*z + 4*d**2*q*s*u*z**2 + 4*d**2*q*s*x*z**2 - 2*d**2*r*s**2*u*z - 2*d**2*r*s**2*x*z - 2*d**2*r*s*u*z**2 - 2*d**2*r*s*x*z**2 + 6*d*f*g*p**2*s**2 - 6*d*f*h*p**2*s**2 - 18*d*g*p**2*q*s**2 + 12*d*g*p**2*r*s**2 + 24*d*h*p**2*q*s**2 - 18*d*h*p**2*r*s**2 - 6*d*l*p**2*q*s**2 + 6*d*l*p**2*r*s**2 + 4*f*g*p**2*s**3 - 8*f*h*p**2*s**3 + 4*f*l*p**2*s**3 - 8*g*p**2*q*s**3 + 4*g*p**2*r*s**3 + 16*h*p**2*q*s**3 - 8*h*p**2*r*s**3 - 8*l*p**2*q*s**3 + 4*l*p**2*r*s**3) / (d**4*p**2)
    a2 = (+2*a*d**4*k - a*d**4*u - a*d**4*x + 4*a*d**3*k*p + 4*a*d**3*k*s + 8*a*d**3*k*z - 4*a*d**3*p*x - 2*a*d**3*s*u - 2*a*d**3*s*x - 4*a*d**3*u*z - 4*a*d**3*x*z + 4*a*d**2*k*p*s + 2*a*d**2*k*p*z + 2*a*d**2*k*s**2 + 8*a*d**2*k*s*z + 2*a*d**2*k*z**2 + 6*a*d**2*m*p**2 - 6*a*d**2*n*p**2 + a*d**2*o*p**2 - a*d**2*p**2*x - 4*a*d**2*p*s*x - 2*a*d**2*p*x*z - a*d**2*s**2*u - a*d**2*s**2*x - 4*a*d**2*s*u*z - 4*a*d**2*s*x*z - a*d**2*u*z**2 - a*d**2*x*z**2 + 12*a*d*m*p**2*s - 18*a*d*n*p**2*s + 6*a*d*o*p**2*s + 6*a*m*p**2*s**2 - 12*a*n*p**2*s**2 + 6*a*o*p**2*s**2 - 4*b*d**3*k*p - 4*b*d**3*k*s - 8*b*d**3*k*z + 4*b*d**3*p*x + 2*b*d**3*s*u + 2*b*d**3*s*x + 4*b*d**3*u*z + 4*b*d**3*x*z - 8*b*d**2*k*p*s - 4*b*d**2*k*p*z - 4*b*d**2*k*s**2 - 16*b*d**2*k*s*z - 4*b*d**2*k*z**2 - 6*b*d**2*m*p**2 + 4*b*d**2*n*p**2 + 2*b*d**2*p**2*x + 8*b*d**2*p*s*x + 4*b*d**2*p*x*z + 2*b*d**2*s**2*u + 2*b*d**2*s**2*x + 8*b*d**2*s*u*z + 8*b*d**2*s*x*z + 2*b*d**2*u*z**2 + 2*b*d**2*x*z**2 - 18*b*d*m*p**2*s + 24*b*d*n*p**2*s - 6*b*d*o*p**2*s - 12*b*m*p**2*s**2 + 24*b*n*p**2*s**2 - 12*b*o*p**2*s**2 + 4*c*d**2*k*p*s + 2*c*d**2*k*p*z + 2*c*d**2*k*s**2 + 8*c*d**2*k*s*z + 2*c*d**2*k*z**2 + c*d**2*m*p**2 - c*d**2*p**2*x - 4*c*d**2*p*s*x - 2*c*d**2*p*x*z - c*d**2*s**2*u - c*d**2*s**2*x - 4*c*d**2*s*u*z - 4*c*d**2*s*x*z - c*d**2*u*z**2 - c*d**2*x*z**2 + 6*c*d*m*p**2*s - 6*c*d*n*p**2*s + 6*c*m*p**2*s**2 - 12*c*n*p**2*s**2 + 6*c*o*p**2*s**2 - 2*d**4*g*v + d**4*g*w + d**4*g*y - 2*d**4*k*r + 2*d**4*m*v - d**4*m*w - d**4*m*y + d**4*r*u + d**4*r*x - 4*d**3*g*p*v + 4*d**3*g*p*w - 4*d**3*g*s*v + 2*d**3*g*s*w + 2*d**3*g*s*y - 8*d**3*g*v*z + 4*d**3*g*w*z + 4*d**3*g*y*z + 4*d**3*h*p*v - 4*d**3*h*p*w + 4*d**3*h*s*v - 2*d**3*h*s*w - 2*d**3*h*s*y + 8*d**3*h*v*z - 4*d**3*h*w*z - 4*d**3*h*y*z + 4*d**3*k*p*q - 4*d**3*k*p*r + 4*d**3*k*q*s + 8*d**3*k*q*z - 4*d**3*k*r*s - 8*d**3*k*r*z + 4*d**3*m*p*v - 4*d**3*m*p*w + 4*d**3*m*s*v - 2*d**3*m*s*w - 2*d**3*m*s*y + 8*d**3*m*v*z - 4*d**3*m*w*z - 4*d**3*m*y*z - 4*d**3*n*p*v + 4*d**3*n*p*w - 4*d**3*n*s*v + 2*d**3*n*s*w + 2*d**3*n*s*y - 8*d**3*n*v*z + 4*d**3*n*w*z + 4*d**3*n*y*z - 4*d**3*p*q*x + 4*d**3*p*r*x - 2*d**3*q*s*u - 2*d**3*q*s*x - 4*d**3*q*u*z - 4*d**3*q*x*z + 2*d**3*r*s*u + 2*d**3*r*s*x + 4*d**3*r*u*z + 4*d**3*r*x*z - d**2*f*g*p**2 - 4*d**2*f*k*p*s - 2*d**2*f*k*p*z - 2*d**2*f*k*s**2 - 8*d**2*f*k*s*z - 2*d**2*f*k*z**2 + d**2*f*p**2*x + 4*d**2*f*p*s*x + 2*d**2*f*p*x*z + d**2*f*s**2*u + d**2*f*s**2*x + 4*d**2*f*s*u*z + 4*d**2*f*s*x*z + d**2*f*u*z**2 + d**2*f*x*z**2 + 6*d**2*g*p**2*q - 6*d**2*g*p**2*r + d**2*g*p**2*w - 4*d**2*g*p*s*v + 4*d**2*g*p*s*w - 2*d**2*g*p*v*z + 2*d**2*g*p*w*z - 2*d**2*g*s**2*v + d**2*g*s**2*w + d**2*g*s**2*y - 8*d**2*g*s*v*z + 4*d**2*g*s*w*z + 4*d**2*g*s*y*z - 2*d**2*g*v*z**2 + d**2*g*w*z**2 + d**2*g*y*z**2 - 4*d**2*h*p**2*q + 6*d**2*h*p**2*r - 2*d**2*h*p**2*w + 8*d**2*h*p*s*v - 8*d**2*h*p*s*w + 4*d**2*h*p*v*z - 4*d**2*h*p*w*z + 4*d**2*h*s**2*v - 2*d**2*h*s**2*w - 2*d**2*h*s**2*y + 16*d**2*h*s*v*z - 8*d**2*h*s*w*z - 8*d**2*h*s*y*z + 4*d**2*h*v*z**2 - 2*d**2*h*w*z**2 - 2*d**2*h*y*z**2 + 8*d**2*k*p*q*s + 4*d**2*k*p*q*z - 4*d**2*k*p*r*s - 2*d**2*k*p*r*z + 4*d**2*k*q*s**2 + 16*d**2*k*q*s*z + 4*d**2*k*q*z**2 - 2*d**2*k*r*s**2 - 8*d**2*k*r*s*z - 2*d**2*k*r*z**2 - d**2*l*p**2*r + d**2*l*p**2*w - 4*d**2*l*p*s*v + 4*d**2*l*p*s*w - 2*d**2*l*p*v*z + 2*d**2*l*p*w*z - 2*d**2*l*s**2*v + d**2*l*s**2*w + d**2*l*s**2*y - 8*d**2*l*s*v*z + 4*d**2*l*s*w*z + 4*d**2*l*s*y*z - 2*d**2*l*v*z**2 + d**2*l*w*z**2 + d**2*l*y*z**2 - d**2*m*p**2*w + 4*d**2*m*p*s*v - 4*d**2*m*p*s*w + 2*d**2*m*p*v*z - 2*d**2*m*p*w*z + 2*d**2*m*s**2*v - d**2*m*s**2*w - d**2*m*s**2*y + 8*d**2*m*s*v*z - 4*d**2*m*s*w*z - 4*d**2*m*s*y*z + 2*d**2*m*v*z**2 - d**2*m*w*z**2 - d**2*m*y*z**2 + 2*d**2*n*p**2*w - 8*d**2*n*p*s*v + 8*d**2*n*p*s*w - 4*d**2*n*p*v*z + 4*d**2*n*p*w*z - 4*d**2*n*s**2*v + 2*d**2*n*s**2*w + 2*d**2*n*s**2*y - 16*d**2*n*s*v*z + 8*d**2*n*s*w*z + 8*d**2*n*s*y*z - 4*d**2*n*v*z**2 + 2*d**2*n*w*z**2 + 2*d**2*n*y*z**2 - d**2*o*p**2*w + 4*d**2*o*p*s*v - 4*d**2*o*p*s*w + 2*d**2*o*p*v*z - 2*d**2*o*p*w*z + 2*d**2*o*s**2*v - d**2*o*s**2*w - d**2*o*s**2*y + 8*d**2*o*s*v*z - 4*d**2*o*s*w*z - 4*d**2*o*s*y*z + 2*d**2*o*v*z**2 - d**2*o*w*z**2 - d**2*o*y*z**2 - 2*d**2*p**2*q*x + d**2*p**2*r*x - 8*d**2*p*q*s*x - 4*d**2*p*q*x*z + 4*d**2*p*r*s*x + 2*d**2*p*r*x*z - 2*d**2*q*s**2*u - 2*d**2*q*s**2*x - 8*d**2*q*s*u*z - 8*d**2*q*s*x*z - 2*d**2*q*u*z**2 - 2*d**2*q*x*z**2 + d**2*r*s**2*u + d**2*r*s**2*x + 4*d**2*r*s*u*z + 4*d**2*r*s*x*z + d**2*r*u*z**2 + d**2*r*x*z**2 - 6*d*f*g*p**2*s + 6*d*f*h*p**2*s + 18*d*g*p**2*q*s - 12*d*g*p**2*r*s - 24*d*h*p**2*q*s + 18*d*h*p**2*r*s + 6*d*l*p**2*q*s - 6*d*l*p**2*r*s - 6*f*g*p**2*s**2 + 12*f*h*p**2*s**2 - 6*f*l*p**2*s**2 + 12*g*p**2*q*s**2 - 6*g*p**2*r*s**2 - 24*h*p**2*q*s**2 + 12*h*p**2*r*s**2 + 12*l*p**2*q*s**2 - 6*l*p**2*r*s**2) / (d**4*p**2)
    a3 = (-4*a*d**3*k + 2*a*d**3*u + 2*a*d**3*x - 2*a*d**2*k*p - 4*a*d**2*k*s - 4*a*d**2*k*z + 2*a*d**2*p*x + 2*a*d**2*s*u + 2*a*d**2*s*x + 2*a*d**2*u*z + 2*a*d**2*x*z - 4*a*d*m*p**2 + 6*a*d*n*p**2 - 2*a*d*o*p**2 - 4*a*m*p**2*s + 8*a*n*p**2*s - 4*a*o*p**2*s + 4*b*d**3*k - 2*b*d**3*u - 2*b*d**3*x + 4*b*d**2*k*p + 8*b*d**2*k*s + 8*b*d**2*k*z - 4*b*d**2*p*x - 4*b*d**2*s*u - 4*b*d**2*s*x - 4*b*d**2*u*z - 4*b*d**2*x*z + 6*b*d*m*p**2 - 8*b*d*n*p**2 + 2*b*d*o*p**2 + 8*b*m*p**2*s - 16*b*n*p**2*s + 8*b*o*p**2*s - 2*c*d**2*k*p - 4*c*d**2*k*s - 4*c*d**2*k*z + 2*c*d**2*p*x + 2*c*d**2*s*u + 2*c*d**2*s*x + 2*c*d**2*u*z + 2*c*d**2*x*z - 2*c*d*m*p**2 + 2*c*d*n*p**2 - 4*c*m*p**2*s + 8*c*n*p**2*s - 4*c*o*p**2*s + 4*d**3*g*v - 2*d**3*g*w - 2*d**3*g*y - 4*d**3*h*v + 2*d**3*h*w + 2*d**3*h*y - 4*d**3*k*q + 4*d**3*k*r - 4*d**3*m*v + 2*d**3*m*w + 2*d**3*m*y + 4*d**3*n*v - 2*d**3*n*w - 2*d**3*n*y + 2*d**3*q*u + 2*d**3*q*x - 2*d**3*r*u - 2*d**3*r*x + 2*d**2*f*k*p + 4*d**2*f*k*s + 4*d**2*f*k*z - 2*d**2*f*p*x - 2*d**2*f*s*u - 2*d**2*f*s*x - 2*d**2*f*u*z - 2*d**2*f*x*z + 2*d**2*g*p*v - 2*d**2*g*p*w + 4*d**2*g*s*v - 2*d**2*g*s*w - 2*d**2*g*s*y + 4*d**2*g*v*z - 2*d**2*g*w*z - 2*d**2*g*y*z - 4*d**2*h*p*v + 4*d**2*h*p*w - 8*d**2*h*s*v + 4*d**2*h*s*w + 4*d**2*h*s*y - 8*d**2*h*v*z + 4*d**2*h*w*z + 4*d**2*h*y*z - 4*d**2*k*p*q + 2*d**2*k*p*r - 8*d**2*k*q*s - 8*d**2*k*q*z + 4*d**2*k*r*s + 4*d**2*k*r*z + 2*d**2*l*p*v - 2*d**2*l*p*w + 4*d**2*l*s*v - 2*d**2*l*s*w - 2*d**2*l*s*y + 4*d**2*l*v*z - 2*d**2*l*w*z - 2*d**2*l*y*z - 2*d**2*m*p*v + 2*d**2*m*p*w - 4*d**2*m*s*v + 2*d**2*m*s*w + 2*d**2*m*s*y - 4*d**2*m*v*z + 2*d**2*m*w*z + 2*d**2*m*y*z + 4*d**2*n*p*v - 4*d**2*n*p*w + 8*d**2*n*s*v - 4*d**2*n*s*w - 4*d**2*n*s*y + 8*d**2*n*v*z - 4*d**2*n*w*z - 4*d**2*n*y*z - 2*d**2*o*p*v + 2*d**2*o*p*w - 4*d**2*o*s*v + 2*d**2*o*s*w + 2*d**2*o*s*y - 4*d**2*o*v*z + 2*d**2*o*w*z + 2*d**2*o*y*z + 4*d**2*p*q*x - 2*d**2*p*r*x + 4*d**2*q*s*u + 4*d**2*q*s*x + 4*d**2*q*u*z + 4*d**2*q*x*z - 2*d**2*r*s*u - 2*d**2*r*s*x - 2*d**2*r*u*z - 2*d**2*r*x*z + 2*d*f*g*p**2 - 2*d*f*h*p**2 - 6*d*g*p**2*q + 4*d*g*p**2*r + 8*d*h*p**2*q - 6*d*h*p**2*r - 2*d*l*p**2*q + 2*d*l*p**2*r + 4*f*g*p**2*s - 8*f*h*p**2*s + 4*f*l*p**2*s - 8*g*p**2*q*s + 4*g*p**2*r*s + 16*h*p**2*q*s - 8*h*p**2*r*s - 8*l*p**2*q*s + 4*l*p**2*r*s) / (d**4*p**2)
    a4 = (+2*a*d**2*k - a*d**2*u - a*d**2*x + a*m*p**2 - 2*a*n*p**2 + a*o*p**2 - 4*b*d**2*k + 2*b*d**2*u + 2*b*d**2*x - 2*b*m*p**2 + 4*b*n*p**2 - 2*b*o*p**2 + 2*c*d**2*k - c*d**2*u - c*d**2*x + c*m*p**2 - 2*c*n*p**2 + c*o*p**2 - 2*d**2*f*k + d**2*f*u + d**2*f*x - 2*d**2*g*v + d**2*g*w + d**2*g*y + 4*d**2*h*v - 2*d**2*h*w - 2*d**2*h*y + 4*d**2*k*q - 2*d**2*k*r - 2*d**2*l*v + d**2*l*w + d**2*l*y + 2*d**2*m*v - d**2*m*w - d**2*m*y - 4*d**2*n*v + 2*d**2*n*w + 2*d**2*n*y + 2*d**2*o*v - d**2*o*w - d**2*o*y - 2*d**2*q*u - 2*d**2*q*x + d**2*r*u + d**2*r*x - f*g*p**2 + 2*f*h*p**2 - f*l*p**2 + 2*g*p**2*q - g*p**2*r - 4*h*p**2*q + 2*h*p**2*r + 2*l*p**2*q - l*p**2*r) / (d**4*p**2)
    """

    a0 = (+2*a*d**4*k*p*z + 2*a*d**4*k*z**2 + a*d**4*m*p**2 - a*d**4*p**2*x - 2*a*d**4*p*x*z - a*d**4*u*z**2 - a*d**4*x*z**2 + 4*a*d**3*k*p*s*z + 4*a*d**3*k*s*z**2 + 4*a*d**3*m*p**2*s - 2*a*d**3*n*p**2*s - 2*a*d**3*p**2*s*x - 4*a*d**3*p*s*x*z - 2*a*d**3*s*u*z**2 - 2*a*d**3*s*x*z**2 + 2*a*d**2*k*p*s**2*z + 2*a*d**2*k*s**2*z**2 + 6*a*d**2*m*p**2*s**2 - 6*a*d**2*n*p**2*s**2 + a*d**2*o*p**2*s**2 - a*d**2*p**2*s**2*x - 2*a*d**2*p*s**2*x*z - a*d**2*s**2*u*z**2 - a*d**2*s**2*x*z**2 + 4*a*d*m*p**2*s**3 - 6*a*d*n*p**2*s**3 + 2*a*d*o*p**2*s**3 + a*m*p**2*s**4 - 2*a*n*p**2*s**4 + a*o*p**2*s**4 - 4*b*d**3*k*p*s*z - 4*b*d**3*k*s*z**2 - 2*b*d**3*m*p**2*s + 2*b*d**3*p**2*s*x + 4*b*d**3*p*s*x*z + 2*b*d**3*s*u*z**2 + 2*b*d**3*s*x*z**2 - 4*b*d**2*k*p*s**2*z - 4*b*d**2*k*s**2*z**2 - 6*b*d**2*m*p**2*s**2 + 4*b*d**2*n*p**2*s**2 + 2*b*d**2*p**2*s**2*x + 4*b*d**2*p*s**2*x*z + 2*b*d**2*s**2*u*z**2 + 2*b*d**2*s**2*x*z**2 - 6*b*d*m*p**2*s**3 + 8*b*d*n*p**2*s**3 - 2*b*d*o*p**2*s**3 - 2*b*m*p**2*s**4 + 4*b*n*p**2*s**4 - 2*b*o*p**2*s**4 + 2*c*d**2*k*p*s**2*z + 2*c*d**2*k*s**2*z**2 + c*d**2*m*p**2*s**2 - c*d**2*p**2*s**2*x - 2*c*d**2*p*s**2*x*z - c*d**2*s**2*u*z**2 - c*d**2*s**2*x*z**2 + 2*c*d*m*p**2*s**3 - 2*c*d*n*p**2*s**3 + c*m*p**2*s**4 - 2*c*n*p**2*s**4 + c*o*p**2*s**4 - d**4*g*p**2*r + d**4*g*p**2*w - 2*d**4*g*p*v*z + 2*d**4*g*p*w*z - 2*d**4*g*v*z**2 + d**4*g*w*z**2 + d**4*g*y*z**2 - 2*d**4*k*p*r*z - 2*d**4*k*r*z**2 - d**4*m*p**2*w + 2*d**4*m*p*v*z - 2*d**4*m*p*w*z + 2*d**4*m*v*z**2 - d**4*m*w*z**2 - d**4*m*y*z**2 + d**4*p**2*r*x + 2*d**4*p*r*x*z + d**4*r*u*z**2 + d**4*r*x*z**2 + 2*d**3*g*p**2*q*s - 4*d**3*g*p**2*r*s + 2*d**3*g*p**2*s*w - 4*d**3*g*p*s*v*z + 4*d**3*g*p*s*w*z - 4*d**3*g*s*v*z**2 + 2*d**3*g*s*w*z**2 + 2*d**3*g*s*y*z**2 + 2*d**3*h*p**2*r*s - 2*d**3*h*p**2*s*w + 4*d**3*h*p*s*v*z - 4*d**3*h*p*s*w*z + 4*d**3*h*s*v*z**2 - 2*d**3*h*s*w*z**2 - 2*d**3*h*s*y*z**2 + 4*d**3*k*p*q*s*z - 4*d**3*k*p*r*s*z + 4*d**3*k*q*s*z**2 - 4*d**3*k*r*s*z**2 - 2*d**3*m*p**2*s*w + 4*d**3*m*p*s*v*z - 4*d**3*m*p*s*w*z + 4*d**3*m*s*v*z**2 - 2*d**3*m*s*w*z**2 - 2*d**3*m*s*y*z**2 + 2*d**3*n*p**2*s*w - 4*d**3*n*p*s*v*z + 4*d**3*n*p*s*w*z - 4*d**3*n*s*v*z**2 + 2*d**3*n*s*w*z**2 + 2*d**3*n*s*y*z**2 - 2*d**3*p**2*q*s*x + 2*d**3*p**2*r*s*x - 4*d**3*p*q*s*x*z + 4*d**3*p*r*s*x*z - 2*d**3*q*s*u*z**2 - 2*d**3*q*s*x*z**2 + 2*d**3*r*s*u*z**2 + 2*d**3*r*s*x*z**2 - d**2*f*g*p**2*s**2 - 2*d**2*f*k*p*s**2*z - 2*d**2*f*k*s**2*z**2 + d**2*f*p**2*s**2*x + 2*d**2*f*p*s**2*x*z + d**2*f*s**2*u*z**2 + d**2*f*s**2*x*z**2 + 6*d**2*g*p**2*q*s**2 - 6*d**2*g*p**2*r*s**2 + d**2*g*p**2*s**2*w - 2*d**2*g*p*s**2*v*z + 2*d**2*g*p*s**2*w*z - 2*d**2*g*s**2*v*z**2 + d**2*g*s**2*w*z**2 + d**2*g*s**2*y*z**2 - 4*d**2*h*p**2*q*s**2 + 6*d**2*h*p**2*r*s**2 - 2*d**2*h*p**2*s**2*w + 4*d**2*h*p*s**2*v*z - 4*d**2*h*p*s**2*w*z + 4*d**2*h*s**2*v*z**2 - 2*d**2*h*s**2*w*z**2 - 2*d**2*h*s**2*y*z**2 + 4*d**2*k*p*q*s**2*z - 2*d**2*k*p*r*s**2*z + 4*d**2*k*q*s**2*z**2 - 2*d**2*k*r*s**2*z**2 - d**2*l*p**2*r*s**2 + d**2*l*p**2*s**2*w - 2*d**2*l*p*s**2*v*z + 2*d**2*l*p*s**2*w*z - 2*d**2*l*s**2*v*z**2 + d**2*l*s**2*w*z**2 + d**2*l*s**2*y*z**2 - d**2*m*p**2*s**2*w + 2*d**2*m*p*s**2*v*z - 2*d**2*m*p*s**2*w*z + 2*d**2*m*s**2*v*z**2 - d**2*m*s**2*w*z**2 - d**2*m*s**2*y*z**2 + 2*d**2*n*p**2*s**2*w - 4*d**2*n*p*s**2*v*z + 4*d**2*n*p*s**2*w*z - 4*d**2*n*s**2*v*z**2 + 2*d**2*n*s**2*w*z**2 + 2*d**2*n*s**2*y*z**2 - d**2*o*p**2*s**2*w + 2*d**2*o*p*s**2*v*z - 2*d**2*o*p*s**2*w*z + 2*d**2*o*s**2*v*z**2 - d**2*o*s**2*w*z**2 - d**2*o*s**2*y*z**2 - 2*d**2*p**2*q*s**2*x + d**2*p**2*r*s**2*x - 4*d**2*p*q*s**2*x*z + 2*d**2*p*r*s**2*x*z - 2*d**2*q*s**2*u*z**2 - 2*d**2*q*s**2*x*z**2 + d**2*r*s**2*u*z**2 + d**2*r*s**2*x*z**2 - 2*d*f*g*p**2*s**3 + 2*d*f*h*p**2*s**3 + 6*d*g*p**2*q*s**3 - 4*d*g*p**2*r*s**3 - 8*d*h*p**2*q*s**3 + 6*d*h*p**2*r*s**3 + 2*d*l*p**2*q*s**3 - 2*d*l*p**2*r*s**3 - f*g*p**2*s**4 + 2*f*h*p**2*s**4 - f*l*p**2*s**4 + 2*g*p**2*q*s**4 - g*p**2*r*s**4 - 4*h*p**2*q*s**4 + 2*h*p**2*r*s**4 + 2*l*p**2*q*s**4 - l*p**2*r*s**4) / (d**4*p**2)
    a1 = (-2*a*d**4*k*p - 4*a*d**4*k*z + 2*a*d**4*p*x + 2*a*d**4*u*z + 2*a*d**4*x*z - 4*a*d**3*k*p*s - 4*a*d**3*k*p*z - 8*a*d**3*k*s*z - 4*a*d**3*k*z**2 - 4*a*d**3*m*p**2 + 2*a*d**3*n*p**2 + 2*a*d**3*p**2*x + 4*a*d**3*p*s*x + 4*a*d**3*p*x*z + 4*a*d**3*s*u*z + 4*a*d**3*s*x*z + 2*a*d**3*u*z**2 + 2*a*d**3*x*z**2 - 2*a*d**2*k*p*s**2 - 4*a*d**2*k*p*s*z - 4*a*d**2*k*s**2*z - 4*a*d**2*k*s*z**2 - 12*a*d**2*m*p**2*s + 12*a*d**2*n*p**2*s - 2*a*d**2*o*p**2*s + 2*a*d**2*p**2*s*x + 2*a*d**2*p*s**2*x + 4*a*d**2*p*s*x*z + 2*a*d**2*s**2*u*z + 2*a*d**2*s**2*x*z + 2*a*d**2*s*u*z**2 + 2*a*d**2*s*x*z**2 - 12*a*d*m*p**2*s**2 + 18*a*d*n*p**2*s**2 - 6*a*d*o*p**2*s**2 - 4*a*m*p**2*s**3 + 8*a*n*p**2*s**3 - 4*a*o*p**2*s**3 + 4*b*d**3*k*p*s + 4*b*d**3*k*p*z + 8*b*d**3*k*s*z + 4*b*d**3*k*z**2 + 2*b*d**3*m*p**2 - 2*b*d**3*p**2*x - 4*b*d**3*p*s*x - 4*b*d**3*p*x*z - 4*b*d**3*s*u*z - 4*b*d**3*s*x*z - 2*b*d**3*u*z**2 - 2*b*d**3*x*z**2 + 4*b*d**2*k*p*s**2 + 8*b*d**2*k*p*s*z + 8*b*d**2*k*s**2*z + 8*b*d**2*k*s*z**2 + 12*b*d**2*m*p**2*s - 8*b*d**2*n*p**2*s - 4*b*d**2*p**2*s*x - 4*b*d**2*p*s**2*x - 8*b*d**2*p*s*x*z - 4*b*d**2*s**2*u*z - 4*b*d**2*s**2*x*z - 4*b*d**2*s*u*z**2 - 4*b*d**2*s*x*z**2 + 18*b*d*m*p**2*s**2 - 24*b*d*n*p**2*s**2 + 6*b*d*o*p**2*s**2 + 8*b*m*p**2*s**3 - 16*b*n*p**2*s**3 + 8*b*o*p**2*s**3 - 2*c*d**2*k*p*s**2 - 4*c*d**2*k*p*s*z - 4*c*d**2*k*s**2*z - 4*c*d**2*k*s*z**2 - 2*c*d**2*m*p**2*s + 2*c*d**2*p**2*s*x + 2*c*d**2*p*s**2*x + 4*c*d**2*p*s*x*z + 2*c*d**2*s**2*u*z + 2*c*d**2*s**2*x*z + 2*c*d**2*s*u*z**2 + 2*c*d**2*s*x*z**2 - 6*c*d*m*p**2*s**2 + 6*c*d*n*p**2*s**2 - 4*c*m*p**2*s**3 + 8*c*n*p**2*s**3 - 4*c*o*p**2*s**3 + 2*d**4*g*p*v - 2*d**4*g*p*w + 4*d**4*g*v*z - 2*d**4*g*w*z - 2*d**4*g*y*z + 2*d**4*k*p*r + 4*d**4*k*r*z - 2*d**4*m*p*v + 2*d**4*m*p*w - 4*d**4*m*v*z + 2*d**4*m*w*z + 2*d**4*m*y*z - 2*d**4*p*r*x - 2*d**4*r*u*z - 2*d**4*r*x*z - 2*d**3*g*p**2*q + 4*d**3*g*p**2*r - 2*d**3*g*p**2*w + 4*d**3*g*p*s*v - 4*d**3*g*p*s*w + 4*d**3*g*p*v*z - 4*d**3*g*p*w*z + 8*d**3*g*s*v*z - 4*d**3*g*s*w*z - 4*d**3*g*s*y*z + 4*d**3*g*v*z**2 - 2*d**3*g*w*z**2 - 2*d**3*g*y*z**2 - 2*d**3*h*p**2*r + 2*d**3*h*p**2*w - 4*d**3*h*p*s*v + 4*d**3*h*p*s*w - 4*d**3*h*p*v*z + 4*d**3*h*p*w*z - 8*d**3*h*s*v*z + 4*d**3*h*s*w*z + 4*d**3*h*s*y*z - 4*d**3*h*v*z**2 + 2*d**3*h*w*z**2 + 2*d**3*h*y*z**2 - 4*d**3*k*p*q*s - 4*d**3*k*p*q*z + 4*d**3*k*p*r*s + 4*d**3*k*p*r*z - 8*d**3*k*q*s*z - 4*d**3*k*q*z**2 + 8*d**3*k*r*s*z + 4*d**3*k*r*z**2 + 2*d**3*m*p**2*w - 4*d**3*m*p*s*v + 4*d**3*m*p*s*w - 4*d**3*m*p*v*z + 4*d**3*m*p*w*z - 8*d**3*m*s*v*z + 4*d**3*m*s*w*z + 4*d**3*m*s*y*z - 4*d**3*m*v*z**2 + 2*d**3*m*w*z**2 + 2*d**3*m*y*z**2 - 2*d**3*n*p**2*w + 4*d**3*n*p*s*v - 4*d**3*n*p*s*w + 4*d**3*n*p*v*z - 4*d**3*n*p*w*z + 8*d**3*n*s*v*z - 4*d**3*n*s*w*z - 4*d**3*n*s*y*z + 4*d**3*n*v*z**2 - 2*d**3*n*w*z**2 - 2*d**3*n*y*z**2 + 2*d**3*p**2*q*x - 2*d**3*p**2*r*x + 4*d**3*p*q*s*x + 4*d**3*p*q*x*z - 4*d**3*p*r*s*x - 4*d**3*p*r*x*z + 4*d**3*q*s*u*z + 4*d**3*q*s*x*z + 2*d**3*q*u*z**2 + 2*d**3*q*x*z**2 - 4*d**3*r*s*u*z - 4*d**3*r*s*x*z - 2*d**3*r*u*z**2 - 2*d**3*r*x*z**2 + 2*d**2*f*g*p**2*s + 2*d**2*f*k*p*s**2 + 4*d**2*f*k*p*s*z + 4*d**2*f*k*s**2*z + 4*d**2*f*k*s*z**2 - 2*d**2*f*p**2*s*x - 2*d**2*f*p*s**2*x - 4*d**2*f*p*s*x*z - 2*d**2*f*s**2*u*z - 2*d**2*f*s**2*x*z - 2*d**2*f*s*u*z**2 - 2*d**2*f*s*x*z**2 - 12*d**2*g*p**2*q*s + 12*d**2*g*p**2*r*s - 2*d**2*g*p**2*s*w + 2*d**2*g*p*s**2*v - 2*d**2*g*p*s**2*w + 4*d**2*g*p*s*v*z - 4*d**2*g*p*s*w*z + 4*d**2*g*s**2*v*z - 2*d**2*g*s**2*w*z - 2*d**2*g*s**2*y*z + 4*d**2*g*s*v*z**2 - 2*d**2*g*s*w*z**2 - 2*d**2*g*s*y*z**2 + 8*d**2*h*p**2*q*s - 12*d**2*h*p**2*r*s + 4*d**2*h*p**2*s*w - 4*d**2*h*p*s**2*v + 4*d**2*h*p*s**2*w - 8*d**2*h*p*s*v*z + 8*d**2*h*p*s*w*z - 8*d**2*h*s**2*v*z + 4*d**2*h*s**2*w*z + 4*d**2*h*s**2*y*z - 8*d**2*h*s*v*z**2 + 4*d**2*h*s*w*z**2 + 4*d**2*h*s*y*z**2 - 4*d**2*k*p*q*s**2 - 8*d**2*k*p*q*s*z + 2*d**2*k*p*r*s**2 + 4*d**2*k*p*r*s*z - 8*d**2*k*q*s**2*z - 8*d**2*k*q*s*z**2 + 4*d**2*k*r*s**2*z + 4*d**2*k*r*s*z**2 + 2*d**2*l*p**2*r*s - 2*d**2*l*p**2*s*w + 2*d**2*l*p*s**2*v - 2*d**2*l*p*s**2*w + 4*d**2*l*p*s*v*z - 4*d**2*l*p*s*w*z + 4*d**2*l*s**2*v*z - 2*d**2*l*s**2*w*z - 2*d**2*l*s**2*y*z + 4*d**2*l*s*v*z**2 - 2*d**2*l*s*w*z**2 - 2*d**2*l*s*y*z**2 + 2*d**2*m*p**2*s*w - 2*d**2*m*p*s**2*v + 2*d**2*m*p*s**2*w - 4*d**2*m*p*s*v*z + 4*d**2*m*p*s*w*z - 4*d**2*m*s**2*v*z + 2*d**2*m*s**2*w*z + 2*d**2*m*s**2*y*z - 4*d**2*m*s*v*z**2 + 2*d**2*m*s*w*z**2 + 2*d**2*m*s*y*z**2 - 4*d**2*n*p**2*s*w + 4*d**2*n*p*s**2*v - 4*d**2*n*p*s**2*w + 8*d**2*n*p*s*v*z - 8*d**2*n*p*s*w*z + 8*d**2*n*s**2*v*z - 4*d**2*n*s**2*w*z - 4*d**2*n*s**2*y*z + 8*d**2*n*s*v*z**2 - 4*d**2*n*s*w*z**2 - 4*d**2*n*s*y*z**2 + 2*d**2*o*p**2*s*w - 2*d**2*o*p*s**2*v + 2*d**2*o*p*s**2*w - 4*d**2*o*p*s*v*z + 4*d**2*o*p*s*w*z - 4*d**2*o*s**2*v*z + 2*d**2*o*s**2*w*z + 2*d**2*o*s**2*y*z - 4*d**2*o*s*v*z**2 + 2*d**2*o*s*w*z**2 + 2*d**2*o*s*y*z**2 + 4*d**2*p**2*q*s*x - 2*d**2*p**2*r*s*x + 4*d**2*p*q*s**2*x + 8*d**2*p*q*s*x*z - 2*d**2*p*r*s**2*x - 4*d**2*p*r*s*x*z + 4*d**2*q*s**2*u*z + 4*d**2*q*s**2*x*z + 4*d**2*q*s*u*z**2 + 4*d**2*q*s*x*z**2 - 2*d**2*r*s**2*u*z - 2*d**2*r*s**2*x*z - 2*d**2*r*s*u*z**2 - 2*d**2*r*s*x*z**2 + 6*d*f*g*p**2*s**2 - 6*d*f*h*p**2*s**2 - 18*d*g*p**2*q*s**2 + 12*d*g*p**2*r*s**2 + 24*d*h*p**2*q*s**2 - 18*d*h*p**2*r*s**2 - 6*d*l*p**2*q*s**2 + 6*d*l*p**2*r*s**2 + 4*f*g*p**2*s**3 - 8*f*h*p**2*s**3 + 4*f*l*p**2*s**3 - 8*g*p**2*q*s**3 + 4*g*p**2*r*s**3 + 16*h*p**2*q*s**3 - 8*h*p**2*r*s**3 - 8*l*p**2*q*s**3 + 4*l*p**2*r*s**3) / (d**4*p**2)
    a2 = (+2*a*d**4*k - a*d**4*u - a*d**4*x + 4*a*d**3*k*p + 4*a*d**3*k*s + 8*a*d**3*k*z - 4*a*d**3*p*x - 2*a*d**3*s*u - 2*a*d**3*s*x - 4*a*d**3*u*z - 4*a*d**3*x*z + 4*a*d**2*k*p*s + 2*a*d**2*k*p*z + 2*a*d**2*k*s**2 + 8*a*d**2*k*s*z + 2*a*d**2*k*z**2 + 6*a*d**2*m*p**2 - 6*a*d**2*n*p**2 + a*d**2*o*p**2 - a*d**2*p**2*x - 4*a*d**2*p*s*x - 2*a*d**2*p*x*z - a*d**2*s**2*u - a*d**2*s**2*x - 4*a*d**2*s*u*z - 4*a*d**2*s*x*z - a*d**2*u*z**2 - a*d**2*x*z**2 + 12*a*d*m*p**2*s - 18*a*d*n*p**2*s + 6*a*d*o*p**2*s + 6*a*m*p**2*s**2 - 12*a*n*p**2*s**2 + 6*a*o*p**2*s**2 - 4*b*d**3*k*p - 4*b*d**3*k*s - 8*b*d**3*k*z + 4*b*d**3*p*x + 2*b*d**3*s*u + 2*b*d**3*s*x + 4*b*d**3*u*z + 4*b*d**3*x*z - 8*b*d**2*k*p*s - 4*b*d**2*k*p*z - 4*b*d**2*k*s**2 - 16*b*d**2*k*s*z - 4*b*d**2*k*z**2 - 6*b*d**2*m*p**2 + 4*b*d**2*n*p**2 + 2*b*d**2*p**2*x + 8*b*d**2*p*s*x + 4*b*d**2*p*x*z + 2*b*d**2*s**2*u + 2*b*d**2*s**2*x + 8*b*d**2*s*u*z + 8*b*d**2*s*x*z + 2*b*d**2*u*z**2 + 2*b*d**2*x*z**2 - 18*b*d*m*p**2*s + 24*b*d*n*p**2*s - 6*b*d*o*p**2*s - 12*b*m*p**2*s**2 + 24*b*n*p**2*s**2 - 12*b*o*p**2*s**2 + 4*c*d**2*k*p*s + 2*c*d**2*k*p*z + 2*c*d**2*k*s**2 + 8*c*d**2*k*s*z + 2*c*d**2*k*z**2 + c*d**2*m*p**2 - c*d**2*p**2*x - 4*c*d**2*p*s*x - 2*c*d**2*p*x*z - c*d**2*s**2*u - c*d**2*s**2*x - 4*c*d**2*s*u*z - 4*c*d**2*s*x*z - c*d**2*u*z**2 - c*d**2*x*z**2 + 6*c*d*m*p**2*s - 6*c*d*n*p**2*s + 6*c*m*p**2*s**2 - 12*c*n*p**2*s**2 + 6*c*o*p**2*s**2 - 2*d**4*g*v + d**4*g*w + d**4*g*y - 2*d**4*k*r + 2*d**4*m*v - d**4*m*w - d**4*m*y + d**4*r*u + d**4*r*x - 4*d**3*g*p*v + 4*d**3*g*p*w - 4*d**3*g*s*v + 2*d**3*g*s*w + 2*d**3*g*s*y - 8*d**3*g*v*z + 4*d**3*g*w*z + 4*d**3*g*y*z + 4*d**3*h*p*v - 4*d**3*h*p*w + 4*d**3*h*s*v - 2*d**3*h*s*w - 2*d**3*h*s*y + 8*d**3*h*v*z - 4*d**3*h*w*z - 4*d**3*h*y*z + 4*d**3*k*p*q - 4*d**3*k*p*r + 4*d**3*k*q*s + 8*d**3*k*q*z - 4*d**3*k*r*s - 8*d**3*k*r*z + 4*d**3*m*p*v - 4*d**3*m*p*w + 4*d**3*m*s*v - 2*d**3*m*s*w - 2*d**3*m*s*y + 8*d**3*m*v*z - 4*d**3*m*w*z - 4*d**3*m*y*z - 4*d**3*n*p*v + 4*d**3*n*p*w - 4*d**3*n*s*v + 2*d**3*n*s*w + 2*d**3*n*s*y - 8*d**3*n*v*z + 4*d**3*n*w*z + 4*d**3*n*y*z - 4*d**3*p*q*x + 4*d**3*p*r*x - 2*d**3*q*s*u - 2*d**3*q*s*x - 4*d**3*q*u*z - 4*d**3*q*x*z + 2*d**3*r*s*u + 2*d**3*r*s*x + 4*d**3*r*u*z + 4*d**3*r*x*z - d**2*f*g*p**2 - 4*d**2*f*k*p*s - 2*d**2*f*k*p*z - 2*d**2*f*k*s**2 - 8*d**2*f*k*s*z - 2*d**2*f*k*z**2 + d**2*f*p**2*x + 4*d**2*f*p*s*x + 2*d**2*f*p*x*z + d**2*f*s**2*u + d**2*f*s**2*x + 4*d**2*f*s*u*z + 4*d**2*f*s*x*z + d**2*f*u*z**2 + d**2*f*x*z**2 + 6*d**2*g*p**2*q - 6*d**2*g*p**2*r + d**2*g*p**2*w - 4*d**2*g*p*s*v + 4*d**2*g*p*s*w - 2*d**2*g*p*v*z + 2*d**2*g*p*w*z - 2*d**2*g*s**2*v + d**2*g*s**2*w + d**2*g*s**2*y - 8*d**2*g*s*v*z + 4*d**2*g*s*w*z + 4*d**2*g*s*y*z - 2*d**2*g*v*z**2 + d**2*g*w*z**2 + d**2*g*y*z**2 - 4*d**2*h*p**2*q + 6*d**2*h*p**2*r - 2*d**2*h*p**2*w + 8*d**2*h*p*s*v - 8*d**2*h*p*s*w + 4*d**2*h*p*v*z - 4*d**2*h*p*w*z + 4*d**2*h*s**2*v - 2*d**2*h*s**2*w - 2*d**2*h*s**2*y + 16*d**2*h*s*v*z - 8*d**2*h*s*w*z - 8*d**2*h*s*y*z + 4*d**2*h*v*z**2 - 2*d**2*h*w*z**2 - 2*d**2*h*y*z**2 + 8*d**2*k*p*q*s + 4*d**2*k*p*q*z - 4*d**2*k*p*r*s - 2*d**2*k*p*r*z + 4*d**2*k*q*s**2 + 16*d**2*k*q*s*z + 4*d**2*k*q*z**2 - 2*d**2*k*r*s**2 - 8*d**2*k*r*s*z - 2*d**2*k*r*z**2 - d**2*l*p**2*r + d**2*l*p**2*w - 4*d**2*l*p*s*v + 4*d**2*l*p*s*w - 2*d**2*l*p*v*z + 2*d**2*l*p*w*z - 2*d**2*l*s**2*v + d**2*l*s**2*w + d**2*l*s**2*y - 8*d**2*l*s*v*z + 4*d**2*l*s*w*z + 4*d**2*l*s*y*z - 2*d**2*l*v*z**2 + d**2*l*w*z**2 + d**2*l*y*z**2 - d**2*m*p**2*w + 4*d**2*m*p*s*v - 4*d**2*m*p*s*w + 2*d**2*m*p*v*z - 2*d**2*m*p*w*z + 2*d**2*m*s**2*v - d**2*m*s**2*w - d**2*m*s**2*y + 8*d**2*m*s*v*z - 4*d**2*m*s*w*z - 4*d**2*m*s*y*z + 2*d**2*m*v*z**2 - d**2*m*w*z**2 - d**2*m*y*z**2 + 2*d**2*n*p**2*w - 8*d**2*n*p*s*v + 8*d**2*n*p*s*w - 4*d**2*n*p*v*z + 4*d**2*n*p*w*z - 4*d**2*n*s**2*v + 2*d**2*n*s**2*w + 2*d**2*n*s**2*y - 16*d**2*n*s*v*z + 8*d**2*n*s*w*z + 8*d**2*n*s*y*z - 4*d**2*n*v*z**2 + 2*d**2*n*w*z**2 + 2*d**2*n*y*z**2 - d**2*o*p**2*w + 4*d**2*o*p*s*v - 4*d**2*o*p*s*w + 2*d**2*o*p*v*z - 2*d**2*o*p*w*z + 2*d**2*o*s**2*v - d**2*o*s**2*w - d**2*o*s**2*y + 8*d**2*o*s*v*z - 4*d**2*o*s*w*z - 4*d**2*o*s*y*z + 2*d**2*o*v*z**2 - d**2*o*w*z**2 - d**2*o*y*z**2 - 2*d**2*p**2*q*x + d**2*p**2*r*x - 8*d**2*p*q*s*x - 4*d**2*p*q*x*z + 4*d**2*p*r*s*x + 2*d**2*p*r*x*z - 2*d**2*q*s**2*u - 2*d**2*q*s**2*x - 8*d**2*q*s*u*z - 8*d**2*q*s*x*z - 2*d**2*q*u*z**2 - 2*d**2*q*x*z**2 + d**2*r*s**2*u + d**2*r*s**2*x + 4*d**2*r*s*u*z + 4*d**2*r*s*x*z + d**2*r*u*z**2 + d**2*r*x*z**2 - 6*d*f*g*p**2*s + 6*d*f*h*p**2*s + 18*d*g*p**2*q*s - 12*d*g*p**2*r*s - 24*d*h*p**2*q*s + 18*d*h*p**2*r*s + 6*d*l*p**2*q*s - 6*d*l*p**2*r*s - 6*f*g*p**2*s**2 + 12*f*h*p**2*s**2 - 6*f*l*p**2*s**2 + 12*g*p**2*q*s**2 - 6*g*p**2*r*s**2 - 24*h*p**2*q*s**2 + 12*h*p**2*r*s**2 + 12*l*p**2*q*s**2 - 6*l*p**2*r*s**2) / (d**4*p**2)
    a3 = (-4*a*d**3*k + 2*a*d**3*u + 2*a*d**3*x - 2*a*d**2*k*p - 4*a*d**2*k*s - 4*a*d**2*k*z + 2*a*d**2*p*x + 2*a*d**2*s*u + 2*a*d**2*s*x + 2*a*d**2*u*z + 2*a*d**2*x*z - 4*a*d*m*p**2 + 6*a*d*n*p**2 - 2*a*d*o*p**2 - 4*a*m*p**2*s + 8*a*n*p**2*s - 4*a*o*p**2*s + 4*b*d**3*k - 2*b*d**3*u - 2*b*d**3*x + 4*b*d**2*k*p + 8*b*d**2*k*s + 8*b*d**2*k*z - 4*b*d**2*p*x - 4*b*d**2*s*u - 4*b*d**2*s*x - 4*b*d**2*u*z - 4*b*d**2*x*z + 6*b*d*m*p**2 - 8*b*d*n*p**2 + 2*b*d*o*p**2 + 8*b*m*p**2*s - 16*b*n*p**2*s + 8*b*o*p**2*s - 2*c*d**2*k*p - 4*c*d**2*k*s - 4*c*d**2*k*z + 2*c*d**2*p*x + 2*c*d**2*s*u + 2*c*d**2*s*x + 2*c*d**2*u*z + 2*c*d**2*x*z - 2*c*d*m*p**2 + 2*c*d*n*p**2 - 4*c*m*p**2*s + 8*c*n*p**2*s - 4*c*o*p**2*s + 4*d**3*g*v - 2*d**3*g*w - 2*d**3*g*y - 4*d**3*h*v + 2*d**3*h*w + 2*d**3*h*y - 4*d**3*k*q + 4*d**3*k*r - 4*d**3*m*v + 2*d**3*m*w + 2*d**3*m*y + 4*d**3*n*v - 2*d**3*n*w - 2*d**3*n*y + 2*d**3*q*u + 2*d**3*q*x - 2*d**3*r*u - 2*d**3*r*x + 2*d**2*f*k*p + 4*d**2*f*k*s + 4*d**2*f*k*z - 2*d**2*f*p*x - 2*d**2*f*s*u - 2*d**2*f*s*x - 2*d**2*f*u*z - 2*d**2*f*x*z + 2*d**2*g*p*v - 2*d**2*g*p*w + 4*d**2*g*s*v - 2*d**2*g*s*w - 2*d**2*g*s*y + 4*d**2*g*v*z - 2*d**2*g*w*z - 2*d**2*g*y*z - 4*d**2*h*p*v + 4*d**2*h*p*w - 8*d**2*h*s*v + 4*d**2*h*s*w + 4*d**2*h*s*y - 8*d**2*h*v*z + 4*d**2*h*w*z + 4*d**2*h*y*z - 4*d**2*k*p*q + 2*d**2*k*p*r - 8*d**2*k*q*s - 8*d**2*k*q*z + 4*d**2*k*r*s + 4*d**2*k*r*z + 2*d**2*l*p*v - 2*d**2*l*p*w + 4*d**2*l*s*v - 2*d**2*l*s*w - 2*d**2*l*s*y + 4*d**2*l*v*z - 2*d**2*l*w*z - 2*d**2*l*y*z - 2*d**2*m*p*v + 2*d**2*m*p*w - 4*d**2*m*s*v + 2*d**2*m*s*w + 2*d**2*m*s*y - 4*d**2*m*v*z + 2*d**2*m*w*z + 2*d**2*m*y*z + 4*d**2*n*p*v - 4*d**2*n*p*w + 8*d**2*n*s*v - 4*d**2*n*s*w - 4*d**2*n*s*y + 8*d**2*n*v*z - 4*d**2*n*w*z - 4*d**2*n*y*z - 2*d**2*o*p*v + 2*d**2*o*p*w - 4*d**2*o*s*v + 2*d**2*o*s*w + 2*d**2*o*s*y - 4*d**2*o*v*z + 2*d**2*o*w*z + 2*d**2*o*y*z + 4*d**2*p*q*x - 2*d**2*p*r*x + 4*d**2*q*s*u + 4*d**2*q*s*x + 4*d**2*q*u*z + 4*d**2*q*x*z - 2*d**2*r*s*u - 2*d**2*r*s*x - 2*d**2*r*u*z - 2*d**2*r*x*z + 2*d*f*g*p**2 - 2*d*f*h*p**2 - 6*d*g*p**2*q + 4*d*g*p**2*r + 8*d*h*p**2*q - 6*d*h*p**2*r - 2*d*l*p**2*q + 2*d*l*p**2*r + 4*f*g*p**2*s - 8*f*h*p**2*s + 4*f*l*p**2*s - 8*g*p**2*q*s + 4*g*p**2*r*s + 16*h*p**2*q*s - 8*h*p**2*r*s - 8*l*p**2*q*s + 4*l*p**2*r*s) / (d**4*p**2)
    a4 = (+2*a*d**2*k - a*d**2*u - a*d**2*x + a*m*p**2 - 2*a*n*p**2 + a*o*p**2 - 4*b*d**2*k + 2*b*d**2*u + 2*b*d**2*x - 2*b*m*p**2 + 4*b*n*p**2 - 2*b*o*p**2 + 2*c*d**2*k - c*d**2*u - c*d**2*x + c*m*p**2 - 2*c*n*p**2 + c*o*p**2 - 2*d**2*f*k + d**2*f*u + d**2*f*x - 2*d**2*g*v + d**2*g*w + d**2*g*y + 4*d**2*h*v - 2*d**2*h*w - 2*d**2*h*y + 4*d**2*k*q - 2*d**2*k*r - 2*d**2*l*v + d**2*l*w + d**2*l*y + 2*d**2*m*v - d**2*m*w - d**2*m*y - 4*d**2*n*v + 2*d**2*n*w + 2*d**2*n*y + 2*d**2*o*v - d**2*o*w - d**2*o*y - 2*d**2*q*u - 2*d**2*q*x + d**2*r*u + d**2*r*x - f*g*p**2 + 2*f*h*p**2 - f*l*p**2 + 2*g*p**2*q - g*p**2*r - 4*h*p**2*q + 2*h*p**2*r + 2*l*p**2*q - l*p**2*r) / (d**4*p**2)

    #w, v, y, x, k, u
    #ww, vv, yy, xx, kk, uu

    #print(a, b, c, g, h, l, r, q, f, m, n, o, w, v, y, x, k, u, ww, vv, yy, xx, kk, uu, s, d, z, p)
    #print(a0, a1, a2, a3, a4)

    #3520.9999999999995 -8.263x + 0.005897x^2 -(1.428e-06)x^3 + (6e-11)x^4
    #2350.0 -5.896x + 0.004768x^2 - (1.5e-06)x^3 + (1.52e-10)x^4

    coeff = [a4]
    coeff += [a3]
    coeff += [a2]
    coeff += [a1]
    coeff += [a0]

    r = np.roots(coeff)
    e_exec_time = time.time()
    #print(r)
    solver_exec_time = e_exec_time - s_exec_time

    r = [re(_r) for _r in r if im(_r) == 0]
    r.sort()

    N = len(r)
    K = 0

    while K < N:
        if r[K] >= it.x - eps and r[K] <= it.x + eps:
            r[K] = it.x
        elif r[K] >= it.y - eps and r[K] <= it.y + eps:
            r[K] = it.y

        K += 1

    K = 0
    _r = []

    while K < N:
        if r[K] >= it.x and r[K] <= it.y:
            _r += [r[K]]

        K += 1

    r = _r

    return solver_exec_time, r

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

def get_initial_state(region_wkt, point_str):
    region = loads(region_wkt)

    units = point_str.split(";")
    unit0 = units[0]

    components = unit0.split("#")

    component0 = components[0].split(",")

    x0 = float(component0[0])
    y0 = float(component0[1])

    point = shapely.geometry.Point(x0, y0)

    # Only need to check if the point is inside the region.

    if point.within(region):
        return State.Inside

    return None

    """
    # The objects have at least one point in common and their interiors do not intersect.
    if point.touches(region):
        return State.Touch
    # The object's boundary and interior intersect only with the interior of the other (not its boundary or exterior).
    elif point.within(region):
        return State.Inside
    else:
        return State.Disjoint
    """

def get_states(iregion_wkt, fregion_wkt, point_str):
    inicial_state = None
    final_state = None

    region = loads(iregion_wkt)

    units = point_str.split(";")
    unit0 = units[0]

    components = unit0.split("#")

    component0 = components[0].split(",")
    component1 = components[1].split(",")

    x0 = float(component0[0])
    y0 = float(component0[1])

    point = shapely.geometry.Point(x0, y0)

    # Only need to check if the point is inside the region.

    #if point.within(region):
    #    inicial_state = State.Inside

    if point.touches(region):
        inicial_state = State.Touch
    elif point.within(region):
        inicial_state = State.Inside
    #elif point.intersects(region):
    #    inicial_state = State.Intersect

    region = loads(fregion_wkt)

    x0 = float(component1[0])
    y0 = float(component1[1])

    point = shapely.geometry.Point(x0, y0)

    #if point.within(region):
    #    final_state = State.Inside

    if point.touches(region):
        final_state = State.Touch
    elif point.within(region):
        final_state = State.Inside
    #elif point.intersects(region):
    #    final_state = State.Intersect

    return inicial_state, final_state

def test1(N, mpoint_st, p_linear_traj):
    op_id = [1, 2, 4, 5, 6]
    op_st = ['Intersects', 'Touches', 'Disjoint', 'Contains', 'Within']

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

    #exec_time, solver_exec_time, avg, sec, ssec
    #exec_time, solver_exec_time, avg, sec, ssec
    #exec_time, solver_exec_time, avg, sec, ssec

    #p_linear_traj = False

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

            p_wkt = 'POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))'
            q_wkt = 'POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))'
            mpoint = mpoint_st

            if err_msg != None:
                print_error(-1, err_msg)

            reg_m_segs = get_moving_segs_from_observations(p_wkt, q_wkt, t0, t1)

            if reg_m_segs == None:
                print_error(err_code, err_msg)

            initial_state, final_state = get_states(p_wkt, q_wkt, mpoint)

            mpoint = create_moving_point([mpoint])

            exec_time, solver_exec_time, avg, sec, ssec = intersections_tests(reg_m_segs, mpoint, initial_state, final_state, op, p_linear_traj)

            min_exec_time = min(min_exec_time, exec_time)
            max_exec_time = max(max_exec_time, exec_time)

            min_solver_exec_time = min(min_solver_exec_time, solver_exec_time)
            max_solver_exec_time = max(max_solver_exec_time, solver_exec_time)

            #print(avg)
            t_avg += avg
            k += 1

        t_avg = t_avg / N
        res += [(format(min_exec_time, precision3), format(max_exec_time, precision3), format(min_solver_exec_time, precision3), format(max_solver_exec_time, precision3), format(t_avg, precision))]

    #print('OP;mET,MET,mSET,MSET,AVGET')
    """
    k = 0
    while k < len(res):
        str = op_st[k] + ';'

        for el in res[k]:
           str += el + ';'

        print(str)

        #print(op_st[k],res[k])
        k += 1
    """
    return res
    #sys.exit()

#test_iceberg_mp_int()

"""
	Equals = Within and Contains
	
	802.826,764.752#990.308,633.951#1000,2000

    755,489#825,706.5#895,774#1000,2000
	802.826,764.752#896.5,774.5#990.308,633.951#1000,2000
	802.826,764.752#896.5,624.5#990.308,633.951#1000,2000
	802.826,764.752#896.5,675.5#990.308,633.951#1000,2000
	802.826,764.752#896.5,690.5#990.308,633.951#1000,2000

	Usage examples:
	    disjoint, inside, disjoint
		python mr_mp_pred.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON ((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "755,489#895,774#1000,2000" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"
		
	    disjoint, inside, disjoint, inside, disjoint
		python mr_mp_pred.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON ((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "802.826,764.752#990.308,633.951#1000,2000" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"		
"""

# Tests
"""
tests = []
N = 10
print('Op;mET (sec);MET (sec);mSET (sec);MSET (sec);AVGET %;')
#print('')
#print('Test 1')
tests += [test1(N, '755,489#895,774#1000,2000', False)]
#print('')
#print('Test 2')
tests += [test1(N, '802.826,764.752#990.308,633.951#1000,2000', False)]
#print('')
#print('Test 3')
tests += [test1(N, '802.826,764.752#896.5,690.5#990.308,633.951#1000,2000', True)]

op_st = ['Intersects', 'Touches', 'Disjoint', 'Contains', 'Within']

k = 0
while k < len(op_st):
    for el in tests:
        str = op_st[k] + ';'
        for e in el[k]:
            str += e + ';'

        print(str)

    #print(op_st[k],res[k])
    k += 1

sys.exit()
"""

# 1. get input

begin_exec_time = time.time()
get_params()

p_wkt = str(sys.argv[1])
q_wkt = str(sys.argv[2])

mpoint = str(sys.argv[3])

"""
p_wkt = 'POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))'
q_wkt = 'POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))'
mpoint = '755,489#895,774#1000,2000'

pass_through_control_points = True
print_intersection_information = True
print_solver_execution_time = True

n_samples = 100
interval.x = 1000
interval.y = 2000
epsilon = 0.0000001
precision = '.2f'
operation = 1

get_params()
"""

t0 = 1000
t1 = 2000

if err_msg != None:
    print_error(-1, err_msg)

# 2. create objects

#p_wkt = str(sys.argv[1])
#q_wkt = str(sys.argv[2])

#mpoint = str(sys.argv[3])

#t0 = 1000
#t1 = 2000

# 2.1 get region moving segments from observations

reg_m_segs = get_moving_segs_from_observations(p_wkt, q_wkt, t0, t1)

if reg_m_segs == None:
    print_error(err_code, err_msg)

# 2.2 get point initial state w.r.t the region

#initial_state = get_initial_state(p_wkt, mpoint)

initial_state, final_state = get_states(p_wkt, q_wkt, mpoint)

# 2.3 create the moving point 

mpoint = create_moving_point([mpoint])

# >>>
"""
mp = MovingPoint()
755,489#825,706.5#895,774#1000,2000

x0 = 755
y0 = 489

x1 = (755 + 895) / 2
y1 = (489 + 774) / 2 + 75

x2 = 895
y2 = 774

i = Interval(float(1000), float(2000), True, False)

cc = CCurve()

p0 = Point(float(x0), float(y0))
p1 = Point(float(x1), float(y1))
p2 = Point(float(x2), float(y2))

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

mpoint = mp
"""
# <<<

# 2.4 get the intersections betwen the two objects

if operation == Operation.Intersects.value \
or operation == Operation.Disjoint.value \
or operation == Operation.Within.value \
or operation == Operation.Touches.value \
or operation == Operation.Contains.value \
or operation == STOperation.Intersection.value:
    get_mr_mp_intersections(reg_m_segs, mpoint, initial_state, final_state, operation, p_linear_traj)
else:
    if operation == Operation.Equals.value:
        print_error(-1, 'Unsupported operation : Equals!')
    elif operation == Operation.Crosses.value:
        print_error(-1, 'Unsupported operation : Crosses!')
    elif operation == Operation.Overlaps.value:
        print_error(-1, 'Unsupported operation : Overlaps!')
    else:
        print_error(-1, 'Unsupported operation: op code: ' + str(operation) + '!')
