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
#import mpypol

from roots import *
from funcs import from_roots

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

#from pypol import Monomial as MONO, Polynomial as POLY

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
precision0 = '.0f'
#tprecision = '.3f'
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

"""
def find_roots(poly, x):
    r = []
    for _ in xrange(poly.degree):
        next_root = muller(poly, x)
        r.append(next_root)
        poly /= (x - next_root)
    return r
"""

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
    #r1 = quartic(poly1d([a4, a3, a2, a1, a0]))
    #r1 = muller(poly1d([a4, a3, a2, a1, a0]), 10)
    #r1 = find_roots(poly1d([a4, a3, a2, a1, a0]))
    #r1 = ruffini(poly1d([a4, a3, a2, a1, a0]))
    #r1 = durand_kerner(poly1d([a4, a3, a2, a1, a0]))
    
    #print(r)
    #print(r1)    
    #sys.exit()

    # I believe that the result may contain only real solutions since the domain is (explicitly) real?
    #r = [re(_r) for _r in r if im(_r) == 0 and _r >= 0 and _r <= 1]
    #r = [re(_r) for _r in r if im(_r) == 0]
    #r.sort()

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

def test2(N, p_wkt, q_wkt, mpoint_st, p_linear_traj):
    op_id = [1, 2, 4, 5, 6]
    op_st = ['Intersects', 'Touches', 'Disjoint', 'Contains', 'Within']

    #op_id = [1]
    #op_st = ['Intersects']

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

            #p_wkt = 'POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))'
            #q_wkt = 'POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))'
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

        M = len(loads(p_wkt).exterior.coords) - 1

        t_avg = t_avg / N
        res += [(format(min_exec_time, precision3), format(max_exec_time, precision3), format(min_solver_exec_time, precision3), format(max_solver_exec_time, precision3), format(t_avg, precision), str(M))]

    return res

#test_iceberg_mp_int()

def change_coords_precision(p_wkt, precision):
    nwkt = 'POLYGON (('
    p = loads(p_wkt)
    N = len(p.exterior.coords)

    k = 0
    while k < N:
        c = p.exterior.coords[k]
        nwkt += format(c[0], precision) + ' ' + format(c[1], precision)

        if k < N - 1:
            nwkt += ', '

        k += 1

    nwkt += '))'
    return nwkt

"""
	Tests
	python mr_mp_pred-test.py 1

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

get_params()

# Tests
if TESTING:
    p_wkt = 'POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))'
    q_wkt = 'POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))'

    tests = []
    N = NTESTS

    #tests += [test1(N, '755,489#895,774#1000,2000', False)]
    tests += [test2(N, p_wkt, q_wkt, '755,489#895,774#1000,2000', False)]

    #tests += [test1(N, '802.826,764.752#990.308,633.951#1000,2000', False)]
    tests += [test2(N, p_wkt, q_wkt, '802.826,764.752#990.308,633.951#1000,2000', False)]

    #tests += [test1(N, '802.826,764.752#896.5,690.5#990.308,633.951#1000,2000', True)]
    tests += [test2(N, p_wkt, q_wkt, '802.826,764.752#896.5,690.5#990.308,633.951#1000,2000', True)]

    p_wkt = 'Polygon ((625.60285412388361692 848.36828579784025806, 596.34076760988864407 823.55912549249683252, 603.97435539614821209 808.9280822354993461, 620.51379559971064737 811.47261149758583088, 631.32804496357823609 804.47515602684779878, 633.23644191014318494 788.5718481388072405, 613.51634012897261528 763.12655551794205167, 610.33567855136459457 720.50569037799289163, 638.3255004343161545 698.24105933473595087, 668.85985157935442658 691.8797361795195684, 691.12448262261136733 700.14945628130078603, 698.12193809334928574 717.32502880038475723, 689.21608567604641848 739.58965984364169799, 702.57486430200071936 756.12910004720413326, 734.3814800780820633 751.04004152303116371, 741.3789355488199817 724.32248427112267564, 765.551963538641985 717.32502880038475723, 782.7275360577259562 724.95861658664432525, 792.90565310607189531 757.40136467824743249, 785.9081976353339769 781.57439266806920841, 766.18809585416352093 791.11637740089372528, 728.0201569228659082 786.02731887672064204, 736.92600934016866177 805.7474206578912117, 768.09649280072835609 826.73978707010485323, 797.99471163024497855 821.65072854593176999, 801.81150552337476256 838.82630106501574119, 759.82677269894725214 845.18762422023212366, 752.82931722820933373 860.45479979275114601, 747.10412638851471456 878.26650462735676683, 731.20081850047404259 886.53622472913798447, 715.29751061243325694 878.90263694287841645, 718.47817219004139133 864.90772600140257964, 735.65374470912536253 837.55403643397255564, 719.11430450556304095 825.467522439061554, 708.30005514169533853 810.20034686654253164, 702.57486430200071936 790.48024508537207566, 672.04051315696244728 794.29703897850185967, 676.4934393656139946 810.20034686654253164, 675.22117473457069536 829.92044864771310131, 655.5010729534001257 850.91281505992685652, 625.60285412388361692 848.36828579784025806))'
    q_wkt = 'Polygon ((706.70553660468544876 678.20429095876056635, 707.01292790704860636 670.55041367985040779, 709.60827545294705487 664.44461890553407102, 714.26057379424082683 658.57928610521935298, 725.00787080502414028 649.68326754334066209, 739.03582089360338614 642.04406131037194427, 766.40832508741391393 633.80762860441359408, 794.68321414780643863 626.1420051436441554, 809.91912333364246024 628.30923061171438349, 824.53011422889949245 642.57192193123285051, 826.05050035276190101 660.68601420567802052, 815.15041278239073108 679.33450087900723702, 796.99764382460853085 685.18765912119067707, 808.02377513813564747 714.89963107817834498, 826.28528942405046109 734.38130536065818887, 844.95501619525600745 733.6663519357948644, 854.99991537960602273 741.57738137626654407, 856.10034301207963381 752.35428782721305652, 847.22899691343786799 767.07282902075394304, 831.69144302242420963 770.35449913528145771, 814.84752853876852896 761.17987575671327249, 789.38872163783935321 740.80079354888562193, 774.17553373008604467 774.12468068018188205, 781.67273712903715932 790.18118888486515061, 791.86835373579151565 806.18745794874712374, 775.74486001003947422 810.08677707062679474, 760.43449296249832514 785.43121944686799907, 748.63271334742307772 779.54904339876839003, 735.93964009607088883 774.38666630690158854, 724.17953067452106097 771.00648497330303144, 709.31313846120156086 769.93359364380921761, 712.40755336321126379 760.72012525501531854, 746.10339166142466638 765.0902275964135697, 758.14172836322461535 758.67699862267045319, 770.82401169186437073 739.09554811953898934, 780.84899931447830568 717.75221492337630025, 771.55419992269139584 692.19183373611872412, 753.84645257248826056 697.12184270876082337, 735.44916160316620335 699.71382117740677131, 717.78387790044052963 693.29434257310731482, 706.70553660468544876 678.20429095876056635))'

    tests += [test2(N, p_wkt, q_wkt, '707.709,843.823#725.328,782.787#814.051,777.753#1000,2000', True)]

    tests += [test2(N, p_wkt, q_wkt, '765.599,896.680#720.294,747.549#832.299,607.228#1000,2000', True)]

    tests += [test2(N, p_wkt, q_wkt, '765.599,896.680#766.228,760.134#607.030,683.366#1000,2000', True)]
    # D
    #tests += [test2(N, p_wkt, q_wkt, '765.599,896.680#665.550,820.541#668.066,679.591#1000,2000', True)]
    # D
    #tests += [test2(N, p_wkt, q_wkt, '765.599,896.680#665.550,820.541#712.743,635.544#1000,2000', True)]
    # D
    tests += [test2(N, p_wkt, q_wkt, '765.599,896.680#672.471,804.810#712.743,635.544#1000,2000', True)]

    #p_wkt = 'POLYGON ((-29.42189891107522 212.4418884057775, 17.20299459670919 287.4335593760053, 34.40598919341839 298.8214702347401, 51.60898379012758 221.9848506029543, 98.21151934516536 203.8327771118052, 144.8140549002031 92.32443942238537, 191.4165904552409 194.1514052583001, 235.3287274050323 216.7346814685205, 323.1530013046151 142.1940758798211, 387.4934319957428 134.2942303806034, 419.6636473413066 300.2204052331084, 567.6550106885469 307.7910755559449, 597.8058664249862 182.3480677577326, 627.9567221614257 164.0815286679595, 658.107577897865 199.237846900111, 714.5783390585833 311.397389920356, 742.8137196389425 232.8163899758032, 762.2616534360649 327.9871445438652, 801.1575210303097 330.7665690206559, 824.9624377559289 257.8140955141262, 848.7673544815482 256.3318426126881, 872.5722712071674 331.429054957534, 954.0528936694791 177.9339972847913, 1012.997443561659 200.8056810619051, 1042.469718507749 302.4356433739046, 1078.366524039533 361.8362766443266, 1150.160135103102 294.8184393604109, 1170.231308649503 337.8708610648029, 1210.373655742306 230.4622545050169, 1253.700520122664 321.7299756921121, 1297.027384503021 188.9254458619183, 1340.354248883379 325.2910650652001, 1466.209716078554 186.5894341733554, 1604.845730207315 176.7752994861002, 1751.076137621328 301.9634362550224, 1795.669584128057 230.258982549781, 1884.856477141514 277.8675397371993, 1922.485371197518 240.5779652315045, 1997.743159309524 206.3828191219094, 2015.861852717252 180.1437071114296, 2033.98054612498 263.4008095175334, 2052.099239532709 308.7691947553175, 2196.98446981358 227.4891904980367, 2237.97730552313 312.7850275269892, 2319.96297694223 356.1699583403619, 2350.310959124374 292.2205910386664, 2380.658941306518 249.2837307351316, 2411.006923488662 216.2902264299006, 2455.396981584161 341.1175409359252, 2544.177097775159 287.9548395652799, 2593.49685381423 176.8347635680007, 2642.8166098533 184.4089117580962, 2692.136365892371 276.0496189964159, 2718.077318561801 275.26145066317, 2769.959223900662 281.5379733036887, 2839.236614253989 244.2697105096679, 2873.875309430652 220.1663800619456, 2892.418036451291 286.395664648223, 2910.96076347193 310.2705685894768, 2929.503490492569 273.0881238160662, 2976.018824441168 247.0936726677356, 3022.534158389767 198.866883321567, 3069.049492338365 101.4143384907784, 3159.357461454457 113.5457125848988, 3236.471479728241 113.8103086718459, 3278.183038883149 65.26048687392068, 3319.894598038056 195.0188551348962, 3361.606157192963 219.0139546013185, 3449.421291887109 78.43738660358383, 3493.328859234182 82.48464095064389, 3524.401029234602 135.6845842547662, 3555.473199235023 222.4034458511175, 3586.545369235443 215.1795654134856, 3637.435654843517 170.2795871573373, 3662.880797647554 203.3079643167159, 3748.622620210312 155.9315884877202, 3791.852391572168 182.0490532936142, 3878.311934295882 195.1488140103581, 3922.86673984949 172.5953216071468, 3967.421545403099 86.45573728804179, 4011.976350956707 171.4688459778984, 4130.141550147294 127.081910937856, 4205.465780365918 143.1692406102134, 4243.127895475231 87.16587002833799, 4297.621113227968 115.0638379224476, 4322.953530126747 223.0042587311249, 4373.618363924305 94.18996850899755, 4406.301661149944 86.16687073640819, 4438.984958375583 82.3201551318089, 4471.668255601222 263.3591034141509, 4617.870915837891 219.9461814923968, 4737.951379088293 189.8427474216704, 4785.578633760499 272.0165315032161, 4833.205888432704 246.6622067305297, 4880.83314310491 295.2376403537338, 4937.375310163622 147.3684808151998, 4965.646393692979 196.8967262963805, 4984.805308092831 123.5110394657155, 5023.123136892537 233.5579685834317, 5053.166068356111 220.4749691730489, 5113.251931283258 277.9461469949771, 5160.101672928594 253.5497191556665, 5253.801156219266 157.1251282404161, 5338.701504959606 97.81201805007875, 5359.014458376159 71.51859667861309, 5379.327411792713 206.182421081404, 5399.640365209267 81.68175100383513, 5451.554181790542 81.97480247395453, 5477.511090081181 287.1455014076182, 5503.75120579855 241.0532762496256, 5529.991321515919 102.3329614555279, 5556.231437233288 217.2324490567753, 5575.9686705432 124.3735261950909, 5615.443137163023 109.9132597938078, 5644.632965153405 129.3696234550304, 5673.822793143786 169.8234743585433, 5703.012621134168 299.9459573918628, 5750.25321156128 163.365216950439, 5844.734392415506 296.8042665052524, 5972.18757177139 110.4427977259308, 6095.985971548471 81.16066072750999, 6174.114476237482 104.6469396996491, 6213.178728581986 156.8041044511588, 6271.864533051182 112.8384521243518, 6301.207435285779 209.9262697193223, 6392.125291115265 260.8414321371046, 6419.058046963244 211.7556850348964, 6472.923558659202 256.1940291878348, 6516.047218849909 112.6243479954685, 6537.609048945262 62.94733846153137, 6603.495385077006 208.42965167779, 6620.600021656088 24.4844618169742, 6637.704658235169 46.9900118042121, 6654.80929481425 181.4099615674037, 6698.310742429297 149.2015934758813, 6741.812190044343 10.48791077714563, 6785.313637659389 41.70217833630058, 6803.158522342192 53.00400253741087, 6821.003407024993 9.799995775094658, 6838.848291707795 157.7293798125571, 6872.893841352748 40.43300485433363, 6940.984940642653 19.2400734317187, 6988.207981267175 71.78153194401779, 7035.431021891695 196.8666366543214, 7082.654062516217 140.1520166301802, 7164.005863819855 22.65449644210575, 7204.681764471675 20.68472188912244, 7319.052203574469 59.95980277839844, 7381.381855305564 176.1051924383103, 7412.546681171112 59.94295762987689, 7436.779287487471 171.1032802085371, 7461.011893803831 138.8107802585822, 7485.24450012019 174.2334365024441, 7518.770818072053 113.9756623315516, 7585.823453975779 201.4644394572381, 7612.22095639709 206.1625003237045, 7665.015961239712 139.6007394013476, 7717.424532042026 93.35532314921613, 7753.393344942449 152.0298028289719, 7789.362157842873 187.5042412758719, 7825.330970743296 192.7847449756086, 7863.588857404759 69.12464280086431, 7882.71780073549 162.9986816044026, 7912.77524286223 114.3318191263611, 7942.83268498897 238.9785189835497, 7972.89012711571 295.5288209751109, 8067.592672117397 137.8211637935603, 8114.943944618241 229.8022851841144, 8158.596720767309 175.0957037277271, 8180.423108841844 208.7686815360688, 8229.889161967882 139.8711060632639, 8328.821268219959 180.893330734413, 8375.31147479916 271.9583564887945, 8468.291887957561 129.7895719704939, 8524.39106098501 87.01454476441859, 8552.440647498735 168.4645811307875, 8586.134620179786 159.4911365031278, 8602.98160652031 238.6684792817616, 8637.13447427605 80.45042408145245, 8671.28734203179 90.91466028272326, 8705.44020978753 206.731581264186, 8736.281923276636 187.9727680501281, 8767.123636765742 135.8533183629925, 8797.965350254848 210.7912168357741, 8824.328639397094 137.0186106390847, 8850.69192853934 250.4099869273144, 8877.055217681585 123.7070284692624, 8973.156319829593 248.8269737737221, 9020.739987140067 223.7278210431435, 9068.323654450542 32.78031130144474, 9115.907321761015 147.6803219181832, 9218.97067609702 227.694864484071, 9322.117977911765 95.85888610763064, 9449.624433736986 64.70173592534667, 9489.59983533748 26.8187561689507, 9509.587536137728 50.19503321580315, 9604.367918061313 231.0085987816208, 9631.590600045965 123.332028080771, 9686.035964015273 236.1409716218179, 9733.764291101808 183.6596626266819, 9781.492618188342 215.6556171529572, 9829.220945274878 185.0848832963847, 9858.955061349607 203.0524082219231, 9888.689177424334 80.47121050167084, 9918.423293499063 69.79656006274918, 9962.551824494341 189.8215974741253, 10050.8088864849 233.3401322283401, 10079.34442173086 156.2973554535007, 10136.41549222278 127.2007131441475, 10214.48235686889 228.0914528006949, 10290.93777668776 106.7834051500342, 10372.26430160123 178.15502403075, 10437.29749816503 148.3382185958569, 10469.81409644693 184.5695106035396, 10568.54642321821 214.2180005753577, 10617.91258660384 271.1309828140433, 10696.45256633656 256.7887689260863, 10744.27006815037 164.4715542256187, 10792.08756996418 276.436287025404, 10839.90507177799 247.8946164436542, 10868.17442583102 265.5196974224829, 10924.71313393707 238.3144483183113, 11002.2422319651 181.7997096097615, 11026.57928304458 152.3799499729831, 11075.25338520353 219.1508416038823, 11224.62634520636 161.7152395392521, 11286.29048521704 217.9845755412364, 11329.39908772736 165.785247304038, 11350.95338898252 91.75569831958104, 11388.22278217686 164.0313156531717, 11462.76156856553 154.0137387137684, 11525.77282964457 76.526079656946, 11638.08735902299 287.6443982082687, 11733.10415613752 256.5962833241688, 11824.50254310994 232.7344135810091, 11893.39316378372 200.4412472462899, 11927.83847412061 143.7646268606433, 11975.9808153895 221.2949935325917, 12024.12315665839 259.1170215204504, 12072.26549792728 182.6888493269737, 12130.14961976089 307.4085903312518, 12178.69262672382 260.0538878502048, 12275.77864064966 138.2387840436713, 12306.89003515527 113.1486256018167, 12338.00142966089 225.4770866072872, 12369.1128241665 147.0667704040241, 12432.17145985128 261.6647737359312, 12463.70077769367 201.3094080790087, 12481.31716664776 267.1685900463761, 12498.93355560185 231.4254534985192, 12516.54994455594 159.4908263443687, 12615.11690289916 221.7091762886337, 12707.53375063772 135.1747637413034, 12753.742174507 230.5943506988298, 12874.06183717295 181.6037124668378, 12904.14623286328 63.83896691328449, 12934.23062855361 35.96483404699181, 12964.31502424394 193.1636731202793, 13007.82236439297 59.29050318917986, 13094.83704469101 97.58125553424426, 13143.14038962946 150.7819999189317, 13167.29206209868 198.4501704335487, 13261.75329635328 66.3469267103946, 13356.14761396593 71.80884760814351, 13389.06373300182 35.11767906312258, 13454.89597107361 122.3586273107967, 13482.78494673538 68.19186446827374, 13510.67392239715 149.6588739803059, 13538.56289805892 121.1424419202778, 13562.02158573492 159.8768279210979, 13608.93896108692 157.9928647825061, 13699.51928413061 111.223331897195, 13744.80944565245 60.18528329903138, 13770.06452508179 80.92212607583923, 13820.57468394045 132.3613064414006, 13878.81749033182 69.90995666492898, 13907.9388935275 108.0578349092393, 13983.42560584553 172.6033867361062, 14018.7186465392 140.4343701509752, 14089.30472792656 138.063162806642, 14160.86240128488 130.7830155993712, 14206.21435606664 81.85198798717025, 14228.89033345752 75.11351304026104, 14331.26088245135 166.5426171122788, 14408.41743215606 142.4884917232197, 14446.99570700842 41.46566969180058, 14486.04253283889 99.1471818279387, 14564.13618449985 102.996417749271, 14581.3985118338 117.3766009610586, 14615.92316650169 132.9376662886958, 14660.62954846977 190.9497070960116, 14705.33593043785 108.3453869602411, 14750.04231240593 202.0641192372618, 14808.34259869475 72.35168714140175, 14837.49274183917 166.3391289542792, 14872.0610324697 31.71715096515706, 14889.34517778496 172.2120763058758, 14917.33985362393 105.904998653042, 14945.33452946291 70.12435819594785, 14973.32920530188 143.2661503690813, 15113.51205689712 69.87587170447632, 15156.12651135738 27.70596591138052, 15198.74096581765 166.6018841332752, 15241.35542027792 63.95231312252487, 15287.85703725274 97.63591756400579, 15334.35865422757 118.6994863216139, 15380.8602712024 128.4369966786255, 15426.93065710846 69.10575969111338, 15519.07142892058 67.16089265773246, 15539.87368568279 143.1619020358175, 15581.47819920722 112.8842983136844, 15622.12574525454 169.8705836735972, 15703.42083734918 111.5460414273167, 15746.64598877612 161.6628221802025, 15789.87114020305 160.7832821615084, 15833.09629162999 58.13348135279011, 15873.55899348625 161.8137660305296, 15954.48439719878 64.61003091429554, 15989.24037148684 63.8192886569753, 16006.61835863086 137.0160277794354, 16037.84983865088 130.8339393625043, 16069.08131867091 107.8788511247535, 16100.31279869093 52.40409899852141, 16122.55157559378 60.59807338968011, 16144.79035249664 94.89115605520576, 16167.0291293995 46.10125384971521, 16215.17959296206 215.0056130639111, 16311.48052008719 70.2461281691978, 16389.73049318987 119.7887562133408, 16428.85547974121 150.8088997721217, 16448.17501822314 83.79105143482606, 16467.49455670508 164.7539611976625, 16486.81409518702 132.9953402988674, 16589.45355019784 47.57476873792164, 16626.01269309406 46.95256087641282, 16644.29226454217 143.3102339286096, 16706.58875633508 123.435620171047, 16737.73700223154 67.06202095789349, 16812.44224287675 140.3914311727373, 16839.40854891861 163.8877562817348, 16893.34116100233 222.5782315534669, 16966.91448306888 237.9137443401938, 17009.60384326366 114.2669047938759, 17052.29320345843 60.39477529307361, 17094.98256365321 90.39138149862366, 17160.18199868303 275.611666813934, 17199.13236259605 83.12268000359717, 17277.0330904221 263.9735447560079, 17369.3517352926 128.8937445167707, 17415.51105772785 210.1034316729617, 17478.67177978158 293.6535454760401, 17549.62895343834 187.1428298828944, 17585.10754026672 144.6985486576265, 17638.94147013282 209.4139380218248, 17665.85843506587 209.539292380061, 17784.28774927016 152.2396772641132, 17889.69755368181 105.7398160036098, 17917.31404839083 150.4647943297587, 17944.93054309985 221.9596600145815, 17972.54703780887 164.3807778849417, 18043.04379800261 152.5569459295165, 18078.29217809947 119.736922641405, 18135.42351264879 275.5882501389933, 18218.78585520601 303.4923225645707, 18252.98406327194 145.1362939853715, 18270.08316730491 218.7306189211311, 18310.88101998548 333.2715252888154, 18392.47672534662 214.0189107212128, 18413.54869958297 338.597881363135, 18434.62067381933 300.0237010306619, 18455.69264805568 305.5487416256458, 18481.77796885983 334.1812406832939, 18507.86328966399 342.7610906344236, 18533.94861046815 352.2838808186575, 18575.93363924649 318.6370459635372, 18617.91866802483 288.743246220663, 18659.90369680317 340.6303264369218, 18755.48038108187 357.5142791937101, 18803.26872322122 393.5628813438659, 18842.9950483938 427.9393278599511, 18882.72137356638 403.0714965237901, 18922.44769873895 311.5526562493667, 19026.95613149623 360.5327128437947, 19063.99231586818 446.9798022455684, 19101.02850024014 417.5794663982297, 19138.0646846121 356.2366792429224, 19194.55509610794 463.7152521430958, 19222.80030185585 426.8586691248254, 19321.7432007834 458.0138785392977, 19371.21465024718 286.2553076417918, 19435.44634612601 364.8849334372571, 19467.56219406543 457.2307549932773, 19491.9482364059 309.9308695245555, 19540.72032108684 396.7363025162197, 19653.32609338048 346.8640399621216, 19673.89420726423 450.009573640623, 19694.46232114799 350.7088753590567, 19715.03043503175 302.0438568403666, 19743.06119223288 247.8778342519913, 19771.09194943401 426.8121133987935, 19799.12270663515 362.7347764449498, 19844.22413148008 351.8444174602578, 19866.77484390255 376.9469218072848, 19974.68672931902 447.378532122715, 20020.83267314877 286.8768071514214, 20113.12456080827 282.8074745806655, 20132.82179840758 424.0588781589016, 20172.2162736062 336.9422223382373, 20226.92052414955 410.4827054437763, 20290.11045949539 382.7620584841, 20321.70542716831 350.4387224062198, 20408.39536405908 331.663694166473, 20451.74033250447 388.3251092471526, 20573.3865958952 367.6109967732436, 20603.32770809658 325.5703157125121, 20633.26882029796 356.905561263389, 20663.20993249933 337.7799256417366, 20763.37198225062 247.0759634258544, 20832.74939619385 197.3866048140388, 21121.90166900783 124.7639235374131, 20982.1883811105 -61.58119248203002, 20798.06068922223 -116.8641360508973, 20763.37198225062 -168.4690897359632, 20729.98463233352 -52.32608029320114, 20696.59728241643 -203.0736250582984, 20663.20993249933 -185.9965434232781, 20573.3865958952 -30.02250480688011, 20532.83784143163 -165.9509796769063, 20492.28908696805 -22.60201814233297, 20451.74033250447 -129.4857538991384, 20365.0503956137 -86.0897172629877, 20321.70542716831 -65.87866894322698, 20258.51549182247 -154.3697544669909, 20226.92052414955 -114.8208194620845, 20208.68577396843 -20.49342176854555, 20190.45102378732 -3.526655210591031, 20172.2162736062 -105.4624158982296, 20152.51903600689 -7.740244914110264, 20113.12456080827 0.2458697055119217, 20066.97861697852 -125.7688942429451, 19974.68672931902 -123.1686761301338, 19938.71610084686 -110.9323357492416, 19902.74547237471 -39.5760639719802, 19866.77484390255 -104.2209614692682, 19821.67341905761 -73.71320809815191, 19799.12270663515 -11.03866746149296, 19715.03043503175 -31.86538972744111, 19653.32609338048 -123.2981970286188, 19615.79083594926 25.11720647601513, 19578.25557851805 -163.9583678458777, 19540.72032108684 -41.9512943683591, 19516.33427874637 7.661468290640386, 19467.56219406543 26.66134540066741, 19403.33049818659 -25.80164096070104, 19371.21465024718 -36.82491985827016, 19272.27175131963 9.396076429567728, 19222.80030185585 33.65742566988931, 19166.30989036001 8.509281769648879, 19138.0646846121 33.31127889981462, 19026.95613149623 -82.09997097877513, 18992.1199872438 48.42645342413215, 18957.28384299138 -40.73209639275166, 18922.44769873895 39.99797214410808, 18803.26872322122 23.34348534523554, 18707.69203894252 15.39245129194725, 18659.90369680317 -117.220088591662, 18533.94861046815 -104.9311303697174, 18455.69264805568 -168.1741905899488, 18392.47672534662 -219.4456601969389, 18351.67887266605 -74.64565370707757, 18270.08316730491 -222.306318212076, 18235.88495923897 -226.6305551497356, 18218.78585520601 -141.5597231053614, 18190.99840768693 -237.5419328141083, 18163.21096016786 -266.4682859616253, 18135.42351264879 -281.6383163180739, 18116.37973446569 -114.9197590515439, 18097.33595628258 -263.1013451722979, 18078.29217809947 -239.7522501872647, 18007.79541790574 -195.2217983304012, 17972.54703780887 -186.6940706751625, 17889.69755368181 -140.2861854583913, 17854.56095221126 -125.9425745358317, 17819.42435074071 -191.7820125865661, 17784.28774927016 -309.1144810531782, 17744.81131120207 -295.2124240519134, 17705.33487313396 -209.136209507516, 17665.85843506587 -148.1069472609582, 17612.02450519977 -258.8588348569539, 17585.10754026672 -317.7748272599922, 17514.15036660996 -248.2364715131082, 17478.67177978158 -139.1634395727571, 17457.61820576367 -124.291726559388, 17436.56463174576 -144.6278425569362, 17415.51105772785 -187.0027974849854, 17323.19241285735 -197.0399486246345, 17277.0330904221 -136.8986377302535, 17238.08272650908 -256.2540302994088, 17160.18199868303 -297.6800537886508, 17138.44885367309 -176.5656578580945, 17116.71570866315 -215.5701589503896, 17094.98256365321 -247.5787043628029, 16966.91448306888 -327.1435314572512, 16942.39004238003 -246.9950015683917, 16917.86560169118 -259.5781197551426, 16893.34116100233 -281.4001034478482, 16866.37485496047 -349.4934876446436, 16812.44224287675 -338.0059774375068, 16787.54049599502 -331.3519385720984, 16762.63874911328 -250.8312191753474, 16737.73700223154 -297.809562628385, 16675.44051043862 -372.3702576716463, 16644.29226454217 -283.7313073180602, 16607.73312164595 -268.1029052356451, 16589.45355019784 -298.7870682009685, 16555.24039852756 -257.673777653386, 16521.02724685729 -220.9884846991883, 16486.81409518702 -272.0154479134843, 16428.85547974121 -252.7394194424932, 16350.60550663853 -246.6122390778259, 16311.48052008719 -240.6059245765584, 16263.33005652462 -208.9458818982048, 16167.0291293995 -349.0222916480606, 16100.31279869093 -366.2501006097951, 16006.61835863086 -218.0401480692366, 15971.86238434281 -203.033839859329, 15954.48439719878 -309.35812720694, 15914.02169534252 -218.467222505469, 15833.09629162999 -375.9896686295279, 15703.42083734918 -299.2946112607963, 15662.77329130186 -426.9389847967568, 15581.47819920722 -299.5980689725945, 15560.675942445 -324.3535122858734, 15519.07142892058 -417.9321530721742, 15473.00104301452 -295.7690745409061, 15380.8602712024 -228.8007464165885, 15241.35542027792 -305.9344789765692, 15113.51205689712 -301.6377770118377, 15066.78443969871 -359.8834569362189, 15020.05682250029 -249.7758421586327, 14973.32920530188 -280.3244197591221, 14889.34517778496 -348.5135294978567, 14854.77688715443 -320.1280094894865, 14837.49274183917 -279.7511469826064, 14779.19245555034 -361.9065206145219, 14750.04231240593 -342.8859713275665, 14615.92316650169 -227.5327608025336, 14598.66083916774 -361.6728769608484, 14564.13618449985 -227.3358311495308, 14525.08935866937 -220.2265352228276, 14446.99570700842 -277.9227724320382, 14369.83915730371 -309.7263356252988, 14331.26088245135 -323.6973276167955, 14297.13736612008 -331.2317529467974, 14263.0138497888 -216.7209669815837, 14228.89033345752 -306.7852034909938, 14183.53837867576 -276.9608991960104, 14160.86240128488 -399.2163386119594, 14137.00984349878 -230.2779507929528, 14113.15728571267 -276.6183054897568, 14089.30472792656 -321.8995232167957, 14054.01168723288 -204.8964146494024, 13983.42560584553 -354.9139252365242, 13958.26336840618 -263.6865326350119, 13933.10113096684 -211.7495860260767, 13907.9388935275 -247.4729618125764, 13849.69608713613 -414.1150418634672, 13820.57468394045 -423.3012856867308, 13795.31960451112 -335.4900529440255, 13744.80944565245 -282.6622615242006, 13654.22912260877 -267.0452232616577, 13608.93896108692 -245.6825279392289, 13585.48027341092 -237.1762744389094, 13538.56289805892 -324.8881670256424, 13454.89597107361 -228.2636288391336, 13421.97985203772 -331.0172975501071, 13356.14761396593 -278.74506161448, 13324.68284142838 -375.6155787037475, 13293.21806889083 -359.7381875305142, 13261.75329635328 -358.2161020540439, 13230.26621826842 -353.4821930737628, 13198.77914018355 -169.6310928426923, 13167.29206209868 -280.1584379724588, 13118.98871716023 -324.0211012139279, 13094.83704469101 -312.6805501569913, 13051.32970454199 -218.4789258618385, 12964.31502424394 -385.0568851670645, 12874.06183717295 -233.7298296597945, 12833.95528295097 -315.0575595669764, 12793.84872872898 -325.0138798359141, 12753.742174507 -250.9764449499624, 12661.32532676844 -239.4958582710809, 12615.11690289916 -177.0853334821747, 12582.26125011808 -181.6791935641625, 12549.40559733701 -240.7274253318739, 12516.54994455594 -128.9271858248503, 12463.70077769367 -318.5567030308158, 12400.64214200889 -218.1247598303989, 12369.1128241665 -244.1649507871446, 12275.77864064966 -106.7313660391743, 12227.23563368674 -95.46001428131548, 12130.14961976089 -157.38899055568, 12110.85491248302 -256.6313326136541, 12091.56020520515 -158.3560591671853, 12072.26549792728 -206.4655570495481, 11927.83847412061 -196.2988765179659, 11858.94785344683 -139.8707905524571, 11824.50254310994 -291.281235226235, 11794.03641411913 -311.1381666813134, 11763.57028512833 -261.3531273434629, 11733.10415613752 -316.7544475917174, 11701.43189043267 -173.0838708185576, 11669.75962472783 -139.3436363929257, 11638.08735902299 -291.4525737143761, 11600.64918256352 -289.6738873346679, 11563.21100610404 -235.1556743690422, 11525.77282964457 -152.9796512938143, 11504.76907595156 -202.0618483253444, 11483.76532225854 -178.5425095475888, 11462.76156856553 -275.0039648123134, 11425.4921753712 -325.8534050528868, 11350.95338898252 -225.2175007391543, 11307.8447864722 -290.6539509075193, 11286.29048521704 -311.512166078624, 11265.73577188015 -329.5097061105665, 11245.18105854326 -224.5752321354979, 11224.62634520636 -184.1428970253294, 11174.83535853875 -301.5376357935837, 11125.04437187114 -255.8656774379597, 11075.25338520353 -199.2020758803336, 11050.91633412405 -305.1781915112492, 11002.2422319651 -292.2341217637049, 10976.39919928909 -174.9492270790896, 10950.55616661308 -126.3815673530267, 10924.71313393707 -125.6062827309182, 10896.44377988404 -253.2461640104048, 10839.90507177799 -136.3080616562722, 10696.45256633656 -135.5491095288058, 10670.27257309232 -229.3951024547613, 10644.09257984808 -163.9891401402536, 10617.91258660384 -269.0969118646283, 10519.18025983257 -162.9289571569383, 10469.81409644693 -192.651739455376, 10404.78089988313 -133.0319646002526, 10372.26430160123 -123.3108472398637, 10345.15545996341 -252.5817150179516, 10318.04661832558 -301.3804924603966, 10290.93777668776 -335.0667896760152, 10265.45263674814 -325.031160372533, 10239.96749680851 -203.1939484993422, 10214.48235686889 -186.2314526163806, 10188.46006865352 -163.5834065650104, 10162.43778043815 -342.453805372258, 10136.41549222278 -352.5066181370112, 10107.87995697682 -183.6991929631307, 10050.8088864849 -175.9227850077488, 10006.68035548962 -179.2482838369549, 9918.423293499063 -279.7449379761068, 9829.220945274878 -280.7388880816107, 9686.035964015273 -294.1862704095993, 9658.81328203062 -208.6339371165447, 9604.367918061313 -175.3477964802221, 9572.774457420117 -252.0976270868005, 9541.180996778923 -307.6938143956676, 9509.587536137728 -187.6159288641146, 9469.612134537234 -255.8739456541388, 9449.624433736986 -356.3437839033462, 9407.122281795246 -235.1568110005876, 9364.620129853505 -182.3358000873581, 9322.117977911765 -279.4023489587295, 9287.735543973517 -218.2493012191119, 9253.353110035268 -305.8255575109844, 9218.97067609702 -338.1328939577352, 9184.616224651685 -278.9981358568015, 9150.26177320635 -284.4711985223709, 9115.907321761015 -225.3519831298592, 8973.156319829593 -345.9141593325025, 8941.12261911359 -311.129046931852, 8909.088918397589 -257.9487897957821, 8877.055217681585 -163.1201316923824, 8797.965350254848 -301.1018686225936, 8705.44020978753 -331.6716311434758, 8602.98160652031 -328.9571797922242, 8569.28763383926 -212.5077652786501, 8552.440647498735 -251.6981731311035, 8496.341474471286 -251.9261366498827, 8468.291887957561 -264.5851021420133, 8421.80168137836 -126.0908076909142, 8328.821268219959 -258.4254329238759, 8279.355215093921 -283.1405580694112, 8180.423108841844 -158.1368601468063, 8136.770332692776 -287.9653073877651, 8114.943944618241 -115.3551740475611, 8020.241399616554 -235.3085710181267, 7972.89012711571 -227.8025750966893, 7882.71780073549 -304.8103894281406, 7844.459914074027 -339.1488149995503, 7825.330970743296 -228.278237057388, 7717.424532042026 -252.2654272559235, 7699.955008441255 -292.393209645621, 7682.485484840483 -177.4762837761167, 7665.015961239712 -336.7366902136582, 7638.618458818401 -227.5543979284038, 7585.823453975779 -268.5087308797246, 7552.297136023916 -193.0672948793739, 7485.24450012019 -360.5883819558571, 7412.546681171112 -317.3436393866929, 7350.217029440017 -287.2636959378386, 7319.052203574469 -296.4718771792733, 7280.928723873538 -223.2496448156522, 7242.805244172606 -224.5762208597474, 7204.681764471675 -356.8631013623058, 7123.329963168037 -220.5133536294774, 7082.654062516217 -288.6028062632939, 6940.984940642653 -303.0066863268767, 6906.939390997701 -399.3781924285434, 6838.848291707795 -220.4352298963885, 6785.313637659389 -268.7772674955621, 6654.80929481425 -296.0025122086791, 6603.495385077006 -202.9172559007286, 6581.533273033091 -331.3554805198627, 6559.571160989177 -273.6848852607194, 6537.609048945262 -213.7331341491758, 6494.485388754555 -266.1210612214576, 6472.923558659202 -186.2088807892224, 6445.990802811223 -154.4621741487286, 6392.125291115265 -136.7101942554994, 6361.819339172103 -189.7195689866527, 6331.513387228941 -263.373737399897, 6301.207435285779 -286.1464394966773, 6242.521630816584 -301.3373930095228, 6213.178728581986 -189.9954357448228, 6135.050223892976 -323.0801208717701, 6095.985971548471 -154.6405394464424, 6054.719838289444 -249.8452117724442, 6013.453705030417 -227.8910542128341, 5972.18757177139 -217.395437418216, 5929.703178652762 -233.1913690674801, 5887.218785534134 -182.6189280784587, 5844.734392415506 -231.6012117927399, 5797.493801988393 -237.3400957858982, 5703.012621134168 -309.0804843680154, 5615.443137163023 -243.6608990209783, 5595.705903853112 -294.1082546068845, 5556.231437233288 -189.1052225005944, 5477.511090081181 -241.7605570015258, 5425.597273499905 -228.7160880340176, 5399.640365209267 -150.2103424536025, 5338.701504959606 -193.6313842738867, 5310.401388712826 -340.3861803278797, 5282.101272466046 -214.9827931500853, 5253.801156219266 -275.7600830779031, 5206.95141457393 -214.8916717278077, 5113.251931283258 -302.1531311449012, 5083.208999819684 -124.6485725233389, 5023.123136892537 -296.9184802494121, 5003.964222492685 -259.7666119395761, 4965.646393692979 -209.2685616487463, 4909.104226634267 -255.3970405026547, 4880.83314310491 -261.7683031841685, 4737.951379088293 -306.4620100582271, 4697.924558004825 -288.3069048850253, 4657.897736921358 -312.0163730225722, 4617.870915837891 -248.3995272025155, 4569.136695759001 -279.864595084971, 4520.402475680112 -281.1987181915847, 4471.668255601222 -175.9984883459514, 4373.618363924305 -183.5762100093833, 4348.285947025526 -232.3085587202391, 4297.621113227968 -180.3240194912728, 4279.456707310389 -265.884089623566, 4261.292301392809 -186.8062790763069, 4243.127895475231 -169.8385774700441, 4167.803665256606 -169.831968607875, 4130.141550147294 -180.810283007849, 4090.753150417098 -144.169182811604, 4051.364750686903 -253.437699502899, 4011.976350956707 -160.0014727443663, 3878.311934295882 -194.8824663452586, 3835.082162934025 -229.2770697113447, 3748.622620210312 -346.0968324267032, 3720.042012689392 -317.4467054205031, 3691.461405168473 -294.9272288218756, 3662.880797647554 -346.5835361086262, 3611.99051203948 -256.6994949529888, 3586.545369235443 -216.0070661522857, 3493.328859234182 -374.6169347202692, 3405.513724540036 -152.360397284099, 3361.606157192963 -359.9262168281485, 3236.471479728241 -321.7379698065251, 3210.766806970313 -252.6753934179447, 3185.062134212385 -291.9728110732156, 3159.357461454457 -297.704844924422, 3129.254805082426 -173.8284396401238, 3099.152148710396 -255.8576990818253, 3069.049492338365 -263.9128872933874, 2929.503490492569 -174.308851055543, 2873.875309430652 -280.0106052878727, 2804.597919077325 -264.5806525951456, 2769.959223900662 -71.90809130278024, 2744.018271231231 -150.1335480753968, 2692.136365892371 -72.07029495466382, 2544.177097775159 -203.8176388478163, 2499.78703967966 -144.9578811070649, 2411.006923488662 -122.9529284581003, 2319.96297694223 -237.7000238986867, 2278.97014123268 -232.9520346486613, 2196.98446981358 -78.64779317591376, 2148.68939305329 -214.6193671990002, 2100.394316292999 -207.4990705762235, 2052.099239532709 -231.1655683178329, 1997.743159309524 -228.6490953503638, 1960.114265253521 -128.186348871761, 1884.856477141514 -201.3869619261368, 1840.263030634786 -117.7234636591865, 1751.076137621328 -188.5341435302346, 1702.332668483324 -235.8211066122066, 1653.589199345319 -63.17415378573575, 1604.845730207315 -73.79412127671461, 1558.633725497728 -91.32032504064989, 1512.421720788141 -196.3927032499613, 1466.209716078554 -214.7105171926443, 1424.257893680162 -190.5120901180092, 1382.306071281771 -141.6331639089537, 1340.354248883379 -127.4769946282517, 1210.373655742306 -259.1958393763255, 1190.302482195905 -213.69715316956, 1150.160135103102 -64.56839994575483, 1114.263329571317 -74.72731183786797, 1042.469718507749 -117.9051949062625, 983.525168615569 -56.23442477609138, 954.0528936694791 -250.9413722291148, 926.8926861820419 -114.7756350730503, 899.7324786946047 -188.7660924107684, 872.5722712071674 -115.3121022532135, 801.1575210303097 -172.0342663150118, 781.7095872331873 -83.64734190063018, 742.8137196389425 -163.2641954745675, 686.3429584782242 -165.8157387654803, 658.107577897865 -247.7189358976287, 567.6550106885469 -208.4647936521979, 518.3245562394668 -146.0605649781448, 468.9941017903867 -100.6594767548953, 419.6636473413066 -189.289932305751, 355.3232166501789 -174.9300138728896, 323.1530013046151 -289.8983395808669, 279.2408643548238 -231.0827985677815, 191.4165904552409 -291.887809049686, 51.60898379012758 -186.0796494955855, -87.40298034532651 -245.1825945638385, -29.42189891107522 212.4418884057775))'
    #q_wkt = 'POLYGON ((-11.20048498315465 67.39383830216246, 17.20299459670919 82.22390895688162, 34.40598919341839 107.4228257391412, 51.60898379012758 66.80069543697412, 98.21151934516536 47.29870445036766, 144.8140549002031 23.27739705459538, 191.4165904552409 62.71399936813636, 235.3287274050323 61.15736934911757, 323.1530013046151 51.89279053990568, 387.4934319957428 56.62809042653929, 419.6636473413066 122.980181105894, 567.6550106885469 130.5364252507784, 597.8058664249862 95.76406546492161, 627.9567221614257 82.09810910731721, 658.107577897865 103.2334531695417, 714.5783390585833 131.7660812564416, 742.8137196389425 117.0921027793981, 762.2616534360649 114.8262605848527, 801.1575210303097 160.1001132665262, 824.9624377559289 123.1707527212246, 848.7673544815482 112.0864285513078, 872.5722712071674 145.1074685809687, 954.0528936694791 95.56645429026403, 1012.997443561659 111.3895059341422, 1042.469718507749 148.238438088849, 1078.366524039533 167.1726186339318, 1150.160135103102 153.1740068510298, 1170.231308649503 153.4635177929204, 1210.373655742306 118.5190494353021, 1253.700520122664 129.7676882960058, 1297.027384503021 90.3832202620919, 1340.354248883379 147.2678775199426, 1466.209716078554 83.17715625055129, 1604.845730207315 101.4626775181236, 1751.076137621328 154.0481050355266, 1795.669584128057 128.9127150229506, 1884.856477141514 142.5218328339336, 1922.485371197518 111.634588582652, 1997.743159309524 97.12181728526498, 2015.861852717252 80.66698553496643, 2033.98054612498 125.1658608076131, 2052.099239532709 119.2371051750511, 2196.98446981358 120.2152972181767, 2237.97730552313 162.7843986414959, 2319.96297694223 185.1229649168143, 2350.310959124374 161.6857055068405, 2380.658941306518 136.5144602185354, 2411.006923488662 130.1672866566238, 2455.396981584161 156.3680962731289, 2544.177097775159 147.0628934521995, 2593.49685381423 105.1231198425597, 2642.8166098533 109.6203265602118, 2692.136365892371 139.1623551231316, 2718.077318561801 123.1780177677684, 2769.959223900662 132.5442921829641, 2839.236614253989 106.2151621393495, 2873.875309430652 99.55074710041428, 2892.418036451291 93.11233777051297, 2910.96076347193 104.2051315536811, 2929.503490492569 93.1660520053087, 2976.018824441168 79.61649503407672, 3022.534158389767 54.46971098336967, 3069.049492338365 28.23997402774929, 3159.357461454457 17.39435686670444, 3236.471479728241 6.702899609883371, 3278.183038883149 -15.08151827905823, 3319.894598038056 23.98242300614541, 3361.606157192963 54.43580526883601, 3449.421291887109 -3.557199648808671, 3493.328859234182 -11.4334491218176, 3524.401029234602 -8.086741631366573, 3555.473199235023 42.01408786777248, 3586.545369235443 19.32566548997769, 3637.435654843517 22.52864741891392, 3662.880797647554 40.19526711117933, 3748.622620210312 13.57026506959028, 3791.852391572168 19.22334865094378, 3878.311934295882 50.69923394070473, 3922.86673984949 36.47160679763935, 3967.421545403099 2.555647142410152, 4011.976350956707 47.47837764871866, 4130.141550147294 30.54959491284068, 4205.465780365918 34.57050110845846, 4243.127895475231 14.43616471554346, 4297.621113227968 13.6690528425942, 4322.953530126747 49.09298745187641, 4373.618363924305 14.75034650588324, 4406.301661149944 17.68888932500554, 4438.984958375583 17.57143357564684, 4471.668255601222 82.79100969247054, 4617.870915837891 64.14132372118951, 4737.951379088293 55.03008034631696, 4785.578633760499 108.8974826941247, 4833.205888432704 83.21219663552424, 4880.83314310491 100.6397430313283, 4937.375310163622 25.62080875486236, 4965.646393692979 64.40363867950009, 4984.805308092831 45.45321745573481, 5023.123136892537 72.67886221588171, 5053.166068356111 48.43167341689418, 5113.251931283258 88.86026356845861, 5160.101672928594 66.16271124621058, 5253.801156219266 28.33287889976989, 5338.701504959606 5.323944362026861, 5359.014458376159 -2.553375423627159, 5379.327411792713 39.25598167951724, 5399.640365209267 20.02951854906498, 5451.554181790542 8.784885038843862, 5477.511090081181 95.82053677388899, 5503.75120579855 86.70605572399505, 5529.991321515919 32.7967565457706, 5556.231437233288 82.05603892615171, 5575.9686705432 30.66445486330404, 5615.443137163023 43.9681324974098, 5644.632965153405 44.31026299840858, 5673.822793143786 63.16204730218573, 5703.012621134168 90.88974373425646, 5750.25321156128 45.9084369787506, 5844.734392415506 98.8188239216521, 5972.18757177139 34.61682088033245, 6095.985971548471 10.6063025907709, 6174.114476237482 20.61773317881648, 6213.178728581986 37.85530559072282, 6271.864533051182 24.65955390399135, 6301.207435285779 67.42377895977845, 6392.125291115265 90.91621577909829, 6419.058046963244 46.03538579340294, 6472.923558659202 63.31734710098169, 6516.047218849909 -3.487667548381262, 6537.609048945262 -4.420788462285762, 6603.495385077006 29.3882434511944, 6620.600021656088 -41.79194906870958, 6637.704658235169 -42.60626175003458, 6654.80929481425 5.245133306959719, 6698.310742429297 -20.24781070471568, 6741.812190044343 -64.75082394647103, 6785.313637659389 -51.3181679221279, 6803.158522342192 -43.80253739825851, 6821.003407024993 -63.65916805492886, 6838.848291707795 -5.499769846662074, 6872.893841352748 -54.97373040091413, 6940.984940642653 -56.36924127231049, 6988.207981267175 -40.47515579595344, 7035.431021891695 10.32724569549857, 7082.654062516217 -10.40663587932308, 7164.005863819855 -62.79165502634986, 7204.681764471675 -57.34236192466188, 7319.052203574469 -23.53328571178939, 7381.381855305564 4.808756811892913, 7412.546681171112 -27.04411088772298, 7436.779287487471 8.981795328498173, 7461.011893803831 -11.21660988537051, 7485.24450012019 21.61985606326354, 7518.770818072053 -18.37305430512604, 7585.823453975779 29.20207531084788, 7612.22095639709 35.6203119509446, 7665.015961239712 17.37413285046756, 7717.424532042026 10.65288030248983, 7753.393344942449 28.41137773921385, 7789.362157842873 54.64307702820978, 7825.330970743296 40.60933292083369, 7863.588857404759 -3.84937517881769, 7882.71780073549 55.54504147778917, 7912.77524286223 19.23862773141823, 7942.83268498897 62.94062990731304, 7972.89012711571 100.1194585068986, 8067.592672117397 50.70480209712318, 8114.943944618241 88.58181489831675, 8158.596720767309 69.60615709411188, 8180.423108841844 89.23794748073614, 8229.889161967882 39.3723241814306, 8328.821268219959 57.77439218255971, 8375.31147479916 84.57649031523776, 8468.291887957561 32.51435431463399, 8524.39106098501 11.28966693359699, 8552.440647498735 27.89032386385722, 8586.134620179786 26.40353146771724, 8602.98160652031 56.90570556134101, 8637.13447427605 -20.17728225649223, 8671.28734203179 -17.38045266690657, 8705.44020978753 18.48666133054344, 8736.281923276636 24.26727338094403, 8767.123636765742 6.908174959961736, 8797.965350254848 59.15494987248616, 8824.328639397094 28.86312988275454, 8850.69192853934 65.57735327899439, 8877.055217681585 13.77399840745081, 8973.156319829593 44.9388029167681, 9020.739987140067 14.14708610999319, 9068.323654450542 -38.30398195660505, 9115.907321761015 5.497491335471759, 9218.97067609702 46.80220132282957, 9322.117977911765 -10.15590079896673, 9449.624433736986 -20.461497615173, 9489.59983533748 -49.83636917751809, 9509.587536137728 -25.11579079168474, 9604.367918061313 57.98324674428476, 9631.590600045965 14.84284502268897, 9686.035964015273 65.12641829008575, 9733.764291101808 19.57305504952654, 9781.492618188342 37.58537909468126, 9829.220945274878 23.63964818604139, 9858.955061349607 31.62810848818933, 9888.689177424334 -22.74203666842324, 9918.423293499063 -17.21852142318997, 9962.551824494341 37.73784592301539, 10050.8088864849 40.4322961108947, 10079.34442173086 15.24426934150446, 10136.41549222278 11.33218037557762, 10214.48235686889 37.37208948247747, 10290.93777668776 23.48153836668476, 10372.26430160123 56.13188731350159, 10437.29749816503 49.27949221270124, 10469.81409644693 67.87151844614762, 10568.54642321821 73.82447429872389, 10617.91258660384 104.7808363707274, 10696.45256633656 82.25353825556316, 10744.27006815037 57.68565384609605, 10792.08756996418 100.184051831851, 10839.90507177799 87.75847336823594, 10868.17442583102 68.30577659997753, 10924.71313393707 75.13074596743323, 11002.2422319651 66.49965659917929, 11026.57928304458 32.6757186360996, 11075.25338520353 53.97340465854232, 11224.62634520636 24.69364152346244, 11286.29048521704 44.41142747651472, 11329.39908772736 22.34181404302847, 11350.95338898252 11.74639121941152, 11388.22278217686 23.31815419635368, 11462.76156856553 26.74126461126787, 11525.77282964457 7.401674516105442, 11638.08735902299 84.90415907097301, 11733.10415613752 65.18043665329606, 11824.50254310994 71.83629821835231, 11893.39316378372 66.55470417244844, 11927.83847412061 54.70080037062128, 11975.9808153895 94.25602563649437, 12024.12315665839 93.38100096926446, 12072.26549792728 71.33196770219232, 12130.14961976089 113.4665210434945, 12178.69262672382 98.17567262342908, 12275.77864064966 53.8229758742031, 12306.89003515527 31.11082758178735, 12338.00142966089 71.46768058677114, 12369.1128241665 45.28891766865284, 12432.17145985128 72.66593668501699, 12463.70077769367 60.16202359268598, 12481.31716664776 95.78837703896524, 12498.93355560185 71.38091168695243, 12516.54994455594 56.02273254118225, 12615.11690289916 46.84395742564245, 12707.53375063772 13.93568605660599, 12753.742174507 56.41740311287911, 12874.06183717295 19.64566844491319, 12904.14623286328 -37.42572682946149, 12934.23062855361 -43.7804091318858, 12964.31502424394 23.78580886931245, 13007.82236439297 -21.43140162366904, 13094.83704469101 5.053448056318377, 13143.14038962946 17.69204625752794, 13167.29206209868 18.174642710965, 13261.75329635328 -18.9058075353321, 13356.14761396593 -29.12321314747895, 13389.06373300182 -64.55182602306947, 13454.89597107361 -8.148634713942036, 13482.78494673538 -45.84484290288196, 13510.67392239715 -13.73033759340415, 13538.56289805892 -4.025722012187244, 13562.02158573492 2.566613657044044, 13608.93896108692 -4.9369949783958, 13699.51928413061 -31.27297423579927, 13744.80944565245 -49.45557598380384, 13770.06452508179 -54.88206487236184, 13820.57468394045 -36.43940209020445, 13878.81749033182 -55.38137812035683, 13907.9388935275 -43.89447453829152, 13983.42560584553 3.251442662449712, 14018.7186465392 -17.6230118551515, 14089.30472792656 -23.60715304340119, 14160.86240128488 -28.86504582714936, 14206.21435606664 -54.77614693591268, 14228.89033345752 -43.21932902114825, 14331.26088245135 -9.46456905402863, 14408.41743215606 -34.28389404971306, 14446.99570700842 -54.37032699427508, 14486.04253283889 -32.5213261964388, 14564.13618449985 -16.60170964149854, 14581.3985118338 -16.66357116861463, 14615.92316650169 3.816609119126047, 14660.62954846977 8.664854053327007, 14705.33593043785 -5.805669154240752, 14750.04231240593 30.17947629259184, 14808.34259869475 -33.74500152184808, 14837.49274183917 -8.222970772087281, 14872.0610324697 -56.311396851163, 14889.34517778496 -13.65981086468444, 14917.33985362393 -52.83462669889346, 14945.33452946291 -66.81720941477792, 14973.32920530188 -17.76264771109774, 15113.51205689712 -40.80012777762821, 15156.12651135738 -49.70968007416029, 15198.74096581765 0.7847735295019405, 15241.35542027792 -46.47852252660672, 15287.85703725274 -27.1029874425034, 15334.35865422757 -31.12058580844635, 15380.8602712024 -28.32942022169763, 15426.93065710846 -66.54518704505271, 15519.07142892058 -63.28828140420433, 15539.87368568279 -49.33027489805784, 15581.47819920722 -49.53893978773886, 15622.12574525454 -27.32624879478897, 15703.42083734918 -30.68117392772634, 15746.64598877612 -27.29060930495823, 15789.87114020305 -4.381273293961101, 15833.09629162999 -32.25960689770824, 15873.55899348625 -6.093733376732635, 15954.48439719878 -21.97759234353746, 15989.24037148684 -24.01572832373258, 16006.61835863086 8.657961608685021, 16037.84983865088 13.30909457119019, 16069.08131867091 1.916517499329149, 16100.31279869093 -19.15889051309298, 16122.55157559378 -15.16649144850111, 16144.79035249664 -14.26394092591186, 16167.0291293995 -20.85582214471009, 16215.17959296206 50.77943832646917, 16311.48052008719 -15.66712485365485, 16389.73049318987 2.492644834891625, 16428.85547974121 6.955553546011805, 16448.17501822314 -30.26227014397253, 16467.49455670508 -0.2379864415714916, 16486.81409518702 -4.256773511052678, 16589.45355019784 -19.64232889090363, 16626.01269309406 -22.23135467812223, 16644.29226454217 11.40082916070819, 16706.58875633508 -10.44216422917263, 16737.73700223154 -20.09838213845992, 16812.44224287675 3.446570105071245, 16839.40854891861 -7.132555498729479, 16893.34116100233 26.64633490010112, 16966.91448306888 48.19076359176142, 17009.60384326366 -10.05725206300326, 17052.29320345843 -15.52512848583074, 17094.98256365321 2.557961279661452, 17160.18199868303 73.45730754108476, 17199.13236259605 15.17502433729726, 17277.0330904221 88.44351089392123, 17369.3517352926 37.61455883212066, 17415.51105772785 66.71387753348955, 17478.67177978158 102.5046026233966, 17549.62895343834 60.00101171163518, 17585.10754026672 50.1164768584562, 17638.94147013282 68.30037777396817, 17665.85843506587 81.2429773471858, 17784.28774927016 54.01340139481337, 17889.69755368181 39.33789225329497, 17917.31404839083 51.76282574033584, 17944.93054309985 81.09579016932172, 17972.54703780887 61.44515526809094, 18043.04379800261 34.62903647591154, 18078.29217809947 49.02734388126699, 18135.42351264879 110.7864106834865, 18218.78585520601 132.6542390515483, 18252.98406327194 70.59616178646591, 18270.08316730491 108.5068569464751, 18310.88101998548 144.4282661655252, 18392.47672534662 118.5081749184227, 18413.54869958297 153.2863791039191, 18434.62067381933 155.2070397147372, 18455.69264805568 169.9405871043475, 18481.77796885983 168.1005946390359, 18507.86328966399 185.2990611762194, 18533.94861046815 186.6869584346765, 18575.93363924649 190.2258774313451, 18617.91866802483 178.7552088496384, 18659.90369680317 202.1351895426941, 18755.48038108187 217.7744802941599, 18803.26872322122 231.0300614031931, 18842.9950483938 242.2847959877929, 18882.72137356638 235.1138303855647, 18922.44769873895 222.5221332878123, 19026.95613149623 234.916607607557, 19063.99231586818 268.8693137092899, 19101.02850024014 246.335851915464, 19138.0646846121 227.9127484481493, 19194.55509610794 268.6101544890571, 19222.80030185585 264.0742279565538, 19321.7432007834 255.3351650482757, 19371.21465024718 199.1133454708832, 19435.44634612601 212.1019780437673, 19467.56219406543 264.4031880652498, 19491.9482364059 211.9150716098813, 19540.72032108684 229.2856485820494, 19653.32609338048 218.8356139840084, 19673.89420726423 273.2721318879644, 19694.46232114799 223.5369766771046, 19715.03043503175 210.4433112885952, 19743.06119223288 178.7209580775212, 19771.09194943401 232.1799542543784, 19799.12270663515 220.5572403790992, 19844.22413148008 210.4291642064155, 19866.77484390255 230.8513623290922, 19974.68672931902 239.3669389074335, 20020.83267314877 193.3072788359704, 20113.12456080827 193.759543939812, 20132.82179840758 241.625711293002, 20172.2162736062 213.8426268611688, 20226.92052414955 236.0377499543489, 20290.11045949539 231.3830595143621, 20321.70542716831 205.5273822566722, 20408.39536405908 198.5678150287598, 20451.74033250447 211.796147611446, 20573.3865958952 186.2645714534799, 20603.32770809658 167.6943852224463, 20633.26882029796 178.6633732697672, 20663.20993249933 181.9779487432258, 20763.37198225062 136.9297329064539, 20832.74939619385 121.3614213241343, 20964.68439060177 96.90024643112538, 20906.62394595728 26.22980271786239, 20798.06068922223 26.82509267891066, 20763.37198225062 -28.22298401221187, 20729.98463233352 23.53195452450753, 20696.59728241643 -21.33412374635159, 20663.20993249933 -10.88333313074539, 20573.3865958952 47.47210626816527, 20532.83784143163 21.62798097400929, 20492.28908696805 62.42035888326118, 20451.74033250447 24.02925347927948, 20365.0503956137 54.97639489262232, 20321.70542716831 55.31851462584621, 20258.51549182247 43.54005161308179, 20226.92052414955 49.76525684236741, 20208.68577396843 87.16972162678009, 20190.45102378732 101.547433020871, 20172.2162736062 52.01429907974775, 20152.51903600689 82.85387907656921, 20113.12456080827 89.35752016108029, 20066.97861697852 66.39487627661168, 19974.68672931902 35.7899330745025, 19938.71610084686 40.4513078573417, 19902.74547237471 73.77816136823995, 19866.77484390255 36.51816720481929, 19821.67341905761 85.16499159943398, 19799.12270663515 86.43128513055247, 19715.03043503175 80.79536082176296, 19653.32609338048 48.76860125540107, 19615.79083594926 99.21099553021759, 19578.25557851805 40.94793895950133, 19540.72032108684 73.93548315838819, 19516.33427874637 107.6911036883311, 19467.56219406543 104.7792104806748, 19403.33049818659 75.44106871394369, 19371.21465024718 79.34459140588251, 19272.27175131963 115.5665564065626, 19222.80030185585 123.8515805642329, 19166.30989036001 111.8612239405433, 19138.0646846121 115.2334991627658, 19026.95613149623 80.9266467729479, 18992.1199872438 131.078796268099, 18957.28384299138 99.60819073793374, 18922.44769873895 109.4854298133477, 18803.26872322122 100.9102597089455, 18707.69203894252 90.82352699280089, 18659.90369680317 24.62938477852219, 18533.94861046815 15.30473781303357, 18455.69264805568 -14.43094304965492, 18392.47672534662 -47.10672124659767, 18351.67887266605 7.813720863768688, 18270.08316730491 -58.32928640199587, 18235.88495923897 -54.59207021852309, 18218.78585520601 -24.19156987574395, 18190.99840768693 -65.9094916323257, 18163.21096016786 -78.7685827676367, 18135.42351264879 -96.81611020584018, 18116.37973446569 -32.70090459695438, 18097.33595628258 -86.28164951288454, 18078.29217809947 -93.95155852064259, 18007.79541790574 -74.65828476717913, 17972.54703780887 -72.35651662818883, 17889.69755368181 -57.78525885323778, 17854.56095221126 -54.60969536983608, 17819.42435074071 -79.49603543335512, 17784.28774927016 -106.2554802037437, 17744.81131120207 -96.8230017915798, 17705.33487313396 -72.04639272329491, 17665.85843506587 -57.11907013808128, 17612.02450519977 -91.69189136493982, 17585.10754026672 -122.7683715039192, 17514.15036660996 -70.32850476194059, 17478.67177978158 -63.48794790472839, 17457.61820576367 -61.38180870024468, 17436.56463174576 -62.0011585748599, 17415.51105772785 -88.35895565560809, 17323.19241285735 -75.20526836750734, 17277.0330904221 -57.40056078174601, 17238.08272650908 -102.2016806760517, 17160.18199868303 -127.369011497994, 17138.44885367309 -86.73943792232964, 17116.71570866315 -95.64300664475141, 17094.98256365321 -121.8451580858707, 16966.91448306888 -159.9468872330871, 16942.39004238003 -134.4753700080976, 16917.86560169118 -131.8102858375664, 16893.34116100233 -155.8871740265752, 16866.37485496047 -165.7213166085139, 16812.44224287675 -163.0303720535196, 16787.54049599502 -150.6998729906092, 16762.63874911328 -118.0365209246762, 16737.73700223154 -155.2884824813933, 16675.44051043862 -184.0288490796498, 16644.29226454217 -143.5286691384896, 16607.73312164595 -132.5955917232116, 16589.45355019784 -153.2327191542852, 16555.24039852756 -136.9794369782208, 16521.02724685729 -121.3353794524408, 16486.81409518702 -164.9965497497824, 16428.85547974121 -142.4244794653428, 16350.60550663853 -122.4560573219775, 16311.48052008719 -122.8499926371911, 16263.33005652462 -99.13202534994385, 16167.0291293995 -162.6098157544353, 16100.31279869093 -173.2814735199075, 16006.61835863086 -121.4568553405729, 15971.86238434281 -114.1743195110331, 15954.48439719878 -163.0015566280949, 15914.02169534252 -124.3225281616251, 15833.09629162999 -198.9584394924988, 15703.42083734918 -195.6418158228732, 15662.77329130186 -232.0928629914257, 15581.47819920722 -194.2111034954064, 15560.675942445 -213.6870240998883, 15519.07142892058 -253.3315876634795, 15473.00104301452 -196.8613516560962, 15380.8602712024 -157.6294353736542, 15241.35542027792 -174.2351890705485, 15113.51205689712 -178.3617427057573, 15066.78443969871 -196.7564117025627, 15020.05682250029 -167.3095008240934, 14973.32920530188 -183.2541894711339, 14889.34517778496 -212.2269096851505, 14854.77688715443 -190.2709451967031, 14837.49274183917 -176.6623226857867, 14779.19245555034 -170.5932146502313, 14750.04231240593 -176.0626199071184, 14615.92316650169 -140.8048066357338, 14598.66083916774 -185.215850885209, 14564.13618449985 -146.7199216672642, 14525.08935866937 -148.8575395579533, 14446.99570700842 -179.2938477376737, 14369.83915730371 -182.2514060932545, 14331.26088245135 -190.0153278468225, 14297.13736612008 -183.1855018228315, 14263.0138497888 -142.3019150271554, 14228.89033345752 -181.6157599194379, 14183.53837867576 -171.9499997220011, 14160.86240128488 -240.0810208992622, 14137.00984349878 -154.2899597637108, 14113.15728571267 -167.6569488894374, 14089.30472792656 -184.4154929184339, 14054.01168723288 -132.6180424849183, 13983.42560584553 -199.030497296045, 13958.26336840618 -159.8916118812063, 13933.10113096684 -147.5073270029713, 13907.9388935275 -176.8527128139274, 13849.69608713613 -238.558229910094, 13820.57468394045 -215.3259124044107, 13795.31960451112 -200.9763558215987, 13744.80944565245 -164.6878822489819, 13654.22912260877 -159.0221229126749, 13608.93896108692 -155.0243090559868, 13585.48027341092 -136.9697355850871, 13538.56289805892 -167.9210915143854, 13454.89597107361 -150.4260198052131, 13421.97985203772 -177.6866987809917, 13356.14761396593 -176.5081737567644, 13324.68284142838 -197.7485921390829, 13293.21806889083 -179.5792383663529, 13261.75329635328 -166.2844185145009, 13230.26621826842 -165.6857522409207, 13198.77914018355 -99.25292048438737, 13167.29206209868 -135.2124552185736, 13118.98871716023 -142.2480418663528, 13094.83704469101 -138.8861146340082, 13051.32970454199 -115.5351357809323, 12964.31502424394 -214.2066403728723, 12874.06183717295 -134.0175205053543, 12833.95528295097 -157.3265486164678, 12793.84872872898 -156.3721988265375, 12753.742174507 -133.7283446526348, 12661.32532676844 -118.1464538022841, 12615.11690289916 -92.9344271186629, 12582.26125011808 -76.81845729391806, 12549.40559733701 -109.4724206588538, 12516.54994455594 -58.85278025019451, 12463.70077769367 -130.1650049849127, 12400.64214200889 -89.61932870033255, 12369.1128241665 -98.147560692542, 12275.77864064966 -35.71591592951459, 12227.23563368674 -32.28035891285891, 12130.14961976089 -59.4361845253525, 12110.85491248302 -86.59668002306164, 12091.56020520515 -56.57045355001532, 12072.26549792728 -75.66024928778499, 11927.83847412061 -80.27035954032932, 11858.94785344683 -54.47770060800705, 11824.50254310994 -120.3224425260153, 11794.03641411913 -124.4312303861929, 11763.57028512833 -118.2721624176493, 11733.10415613752 -139.9860181497023, 11701.43189043267 -77.32847035705629, 11669.75962472783 -62.03271879938938, 11638.08735902299 -111.3106934334568, 11600.64918256352 -127.3512609416799, 11563.21100610404 -105.8859092657662, 11525.77282964457 -89.75274479545732, 11504.76907595156 -99.87209773040942, 11483.76532225854 -95.41526706177743, 11462.76156856553 -127.6323369317808, 11425.4921753712 -122.1919379313385, 11350.95338898252 -102.9663729137006, 11307.8447864722 -117.1104682759617, 11286.29048521704 -138.9077294067019, 11265.73577188015 -144.9780728385165, 11245.18105854326 -113.9527785606392, 11224.62634520636 -102.6167188622105, 11174.83535853875 -127.9367997290054, 11125.04437187114 -106.7739431108992, 11075.25338520353 -90.7244602415945, 11050.91633412405 -135.5157864950236, 11002.2422319651 -111.8509421300547, 10976.39919928909 -56.41252313140986, 10950.55616661308 -37.75369860473458, 10924.71313393707 -55.10916128127135, 10896.44377988404 -86.54021711482731, 10839.90507177799 -64.03092216302778, 10696.45256633656 -56.36058931738717, 10670.27257309232 -76.89051310212379, 10644.09257984808 -66.47381825051814, 10617.91258660384 -97.18602718408061, 10519.18025983257 -37.51688836466242, 10469.81409644693 -65.21838709045966, 10404.78089988313 -50.89508528684661, 10372.26430160123 -56.1303832399901, 10345.15545996341 -110.1390892793948, 10318.04661832558 -114.4156987857374, 10290.93777668776 -141.3975205814797, 10265.45263674814 -128.8627577489738, 10239.96749680851 -104.9347829928736, 10214.48235686889 -95.04256755853903, 10188.46006865352 -96.79589771733615, 10162.43778043815 -139.1876302743188, 10136.41549222278 -168.2162671748861, 10107.87995697682 -116.7768534071779, 10050.8088864849 -101.8191450920674, 10006.68035548962 -92.24407437016656, 9918.423293499063 -142.2572118169529, 9829.220945274878 -149.2001583050966, 9686.035964015273 -137.5464759592467, 9658.81328203062 -98.21145151970565, 9604.367918061313 -100.6164557502424, 9572.774457420117 -140.5282616572446, 9541.180996778923 -149.2498078521738, 9509.587536137728 -128.97467884277, 9469.612134537234 -136.1420051960579, 9449.624433736986 -178.7285018818907, 9407.122281795246 -128.6700986434916, 9364.620129853505 -99.49467685812147, 9322.117977911765 -140.9783429170253, 9287.735543973517 -128.6027375283937, 9253.353110035268 -138.9147255005187, 9218.97067609702 -152.4101851621095, 9184.616224651685 -136.1065771942005, 9150.26177320635 -133.2040434004659, 9115.907321761015 -120.1730562158333, 8973.156319829593 -174.776573905811, 8941.12261911359 -151.2496438123757, 8909.088918397589 -115.8930915525903, 8877.055217681585 -94.60159010007354, 8797.965350254848 -143.2982437478807, 8705.44020978753 -150.9511935883847, 8602.98160652031 -160.0346567754771, 8569.28763383926 -101.4256533761289, 8552.440647498735 -124.7180428884687, 8496.341474471286 -106.8384183020247, 8468.291887957561 -105.877127381534, 8421.80168137836 -64.48555893251996, 8328.821268219959 -105.3007648808499, 8279.355215093921 -93.53824794699852, 8180.423108841844 -55.90502027297327, 8136.770332692776 -100.5679244580494, 8114.943944618241 -43.35314766928843, 8020.241399616554 -84.94051432260041, 7972.89012711571 -98.13173843367539, 7882.71780073549 -148.6226279435974, 7844.459914074027 -153.8972475062328, 7825.330970743296 -110.5718528011709, 7717.424532042026 -120.4171848562518, 7699.955008441255 -119.087319569912, 7682.485484840483 -87.98848317286523, 7665.015961239712 -161.6916156981042, 7638.618458818401 -114.3041102898067, 7585.823453975779 -147.9828800180348, 7552.297136023916 -121.2743528530182, 7485.24450012019 -179.2081718966526, 7412.546681171112 -171.7585954493144, 7350.217029440017 -159.9534310621774, 7319.052203574469 -168.3769233636937, 7280.928723873538 -149.9541592664192, 7242.805244172606 -136.563572666065, 7204.681764471675 -190.7747920897804, 7123.329963168037 -143.3183323242482, 7082.654062516217 -179.0534483746968, 6940.984940642653 -175.3985122043479, 6906.939390997701 -210.254474742894, 6838.848291707795 -152.0276118858892, 6785.313637659389 -156.6567584377619, 6654.80929481425 -160.2515178580046, 6603.495385077006 -126.5446099478857, 6581.533273033091 -151.6750098630059, 6559.571160989177 -147.2046593506626, 6537.609048945262 -111.7883339426159, 6494.485388754555 -142.7614717576563, 6472.923558659202 -98.3995299410977, 6445.990802811223 -72.6272448459638, 6392.125291115265 -65.77214405732634, 6361.819339172103 -67.77453908214386, 6331.513387228941 -88.67883330477841, 6301.207435285779 -115.0117227497872, 6242.521630816584 -112.3146369554401, 6213.178728581986 -84.89473238912417, 6135.050223892976 -136.3532618567725, 6095.985971548471 -76.38921581525406, 6054.719838289444 -97.11655318562808, 6013.453705030417 -96.9235271626104, 5972.18757177139 -83.67072876900158, 5929.703178652762 -78.37852141105563, 5887.218785534134 -63.20397293257614, 5844.734392415506 -102.6057491345943, 5797.493801988393 -82.07834649472467, 5703.012621134168 -118.826939597221, 5615.443137163023 -99.51454105350791, 5595.705903853112 -116.9440200187541, 5556.231437233288 -73.73635654423147, 5477.511090081181 -102.8979014175504, 5425.597273499905 -94.36781206029778, 5399.640365209267 -82.56023952308132, 5338.701504959606 -105.1040697183395, 5310.401388712826 -146.8417476457106, 5282.101272466046 -107.0486678650145, 5253.801156219266 -126.9332492528684, 5206.95141457393 -98.30742675712482, 5113.251931283258 -126.5856282386943, 5083.208999819684 -59.19123938257206, 5023.123136892537 -115.8538999921849, 5003.964222492685 -84.42094219814513, 4965.646393692979 -88.32598390017185, 4909.104226634267 -113.5069052756648, 4880.83314310491 -105.0006518167399, 4737.951379088293 -117.1884692044308, 4697.924558004825 -124.7314967727115, 4657.897736921358 -113.8671342421998, 4617.870915837891 -90.48028207535104, 4569.136695759001 -103.8457116709047, 4520.402475680112 -94.36191992268243, 4471.668255601222 -73.00876318638568, 4373.618363924305 -81.4931649463265, 4348.285947025526 -108.3731760022939, 4297.621113227968 -94.32691830157677, 4279.456707310389 -123.4234858769577, 4261.292301392809 -94.79407016338912, 4243.127895475231 -91.55547665712407, 4167.803665256606 -81.76193668388991, 4130.141550147294 -82.31918318724973, 4090.753150417098 -54.90859046714363, 4051.364750686903 -93.42990826244881, 4011.976350956707 -80.90040446236279, 3878.311934295882 -103.9809159843695, 3835.082162934025 -116.1485084881279, 3748.622620210312 -166.0764680413338, 3720.042012689392 -170.9513660295779, 3691.461405168473 -162.5347763152039, 3662.880797647554 -163.762519019309, 3611.99051203948 -127.4312229352456, 3586.545369235443 -127.8906025046915, 3493.328859234182 -184.4820734221079, 3405.513724540036 -85.89739332674731, 3361.606157192963 -160.8874815986019, 3236.471479728241 -153.9574441983515, 3210.766806970313 -110.5795424228503, 3185.062134212385 -114.9318181167155, 3159.357461454457 -123.8845862593529, 3129.254805082426 -82.22966341801691, 3099.152148710396 -100.9778766478099, 3069.049492338365 -105.3309692498563, 2929.503490492569 -72.90749718040345, 2873.875309430652 -81.59278126725229, 2804.597919077325 -72.2412825648249, 2769.959223900662 -0.4553000573479427, 2744.018271231231 -25.40921214413304, 2692.136365892371 10.88768202480638, 2544.177097775159 -28.09624149177207, 2499.78703967966 -4.346536767901636, 2411.006923488662 1.232502026957949, 2319.96297694223 -62.0612971524758, 2278.97014123268 -47.55653472891947, 2196.98446981358 9.240097644120638, 2148.68939305329 -32.31844274660813, 2100.394316292999 -52.60490404361188, 2052.099239532709 -46.05627757251474, 1997.743159309524 -65.94948418323905, 1960.114265253521 -12.39911124318395, 1884.856477141514 -43.9472982319656, 1840.263030634786 3.350268477807868, 1751.076137621328 -36.77584804423554, 1702.332668483324 -45.99680635687655, 1653.589199345319 19.06261500557792, 1604.845730207315 -0.0250050727067066, 1558.633725497728 -0.5565602272816772, 1512.421720788141 -46.75320854943577, 1466.209716078554 -60.51903661969361, 1424.257893680162 -55.26907429403126, 1382.306071281771 -37.25415033890775, 1340.354248883379 -33.74419822766385, 1210.373655742306 -57.99489219177073, 1190.302482195905 -42.88919224794617, 1150.160135103102 16.73765501621162, 1114.263329571317 23.52986515745874, 1042.469718507749 3.793886802426189, 983.525168615569 20.6677442321602, 954.0528936694791 -70.49122883847532, 926.8926861820419 -23.04631515154448, 899.7324786946047 -46.40336676797409, 872.5722712071674 -8.634327619523162, 801.1575210303097 -29.59347884643199, 781.7095872331873 -2.313762978710035, 742.8137196389425 -33.61312705870668, 686.3429584782242 -27.53807996290572, 658.107577897865 -61.29172908162957, 567.6550106885469 -53.57521449748664, 518.3245562394668 -34.00570641139152, 468.9941017903867 -13.60152780005244, 419.6636473413066 -70.71634973473274, 355.3232166501789 -65.56209750434002, 323.1530013046151 -93.44045956758151, 279.2408643548238 -84.62992115229765, 191.4165904552409 -121.8674471033517, 51.60898379012758 -77.45336468673725, -29.92997536456074 -94.18856308721851, -11.20048498315465 67.39383830216246))'

    """
    p_wkt = 'Polygon ((-11637.61616249147482449 1091.42775211438902261, -11590.99126898368922411 1166.41942308461693756, -11573.78827438698135666 1177.80733394335175035, -11556.58527979027167021 1100.97071431156587096, -11509.98274423523434962 1082.81864082041670372, -11463.38020868019702903 971.31030313099699924, -11416.77767312515788944 1073.13726896691150614, -11372.86553617536628735 1095.7205451771319531, -11285.04126227578490216 1021.17993958843271685, -11220.70083158465604356 1013.28009408921479917, -11188.53061623909343325 1179.20626894171982713, -11040.53925289185281144 1186.77693926455640394, -11010.38839715541325859 1061.33393146634398363, -10980.23754141897370573 1043.06739237657097874, -10950.08668568253415287 1078.22371060872251292, -10893.61592452181685076 1190.38325362896739534, -10865.3805439414572902 1111.80225368441460887, -10845.93261014433483069 1206.97300825247680223, -10807.03674255008991167 1209.75243272926741156, -10783.23182582447043387 1136.79995922273769793, -10759.42690909885095607 1135.31770632129973819, -10735.62199237323147827 1210.4149186661454678, -10654.14136991091982054 1056.91986099340283545, -10595.19682001874025445 1079.79154477051656613, -10565.72454507265138091 1181.42150708251620017, -10529.82773954086587764 1240.82214035293804955, -10458.03412847729669011 1173.80430306902235316, -10437.96295493089564843 1216.85672477341449849, -10397.82060783809356508 1109.44811821362827686, -10354.49374345773503592 1200.7158394007235529, -10311.16687907737832575 1067.91130957052973827, -10267.84001469701979659 1204.27692877381150538, -10141.98454750184464501 1065.57529788196688969, -10003.34853337308413757 1055.7611631947117985, -9857.11812595907213108 1180.94929996363384817, -9812.52467945234275248 1109.24484625839249929, -9723.33778643888581428 1156.85340344581072713, -9685.70889238288145862 1119.56382894011608187, -9610.45110427087638527 1085.36868283052081097, -9592.33241086314774293 1059.12957082004118092, -9574.21371745541910059 1142.3866732261449215, -9556.09502404769045825 1187.75505846392911735, -9411.2097937668186205 1106.47505420664811027, -9370.21695805726994877 1191.77089123560062944, -9288.23128663816896733 1235.15582204897350493, -9257.88330445602514374 1171.20645474727780311, -9227.53532227388132014 1128.26959444374324448, -9197.18734009173749655 1095.27609013851224518, -9152.79728199623787077 1220.10340464453679488, -9064.0171658052404382 1166.94070327389135855, -9014.69740976616958505 1055.8206272766121856, -8965.37765372709873191 1063.39477546670786978, -8916.05789768802787876 1155.0354827050273343, -8890.11694501859892625 1154.24731437178161286, -8838.23503967973738327 1160.52383701230019142, -8768.95764932641031919 1123.25557421827943472, -8734.31895414974678715 1099.15224377055710647, -8715.77622712910851988 1165.38152835683445119, -8697.23350010846843361 1189.25643229808838441, -8678.69077308783016633 1152.07398752467770464, -8632.17543913923145737 1126.07953637634727784, -8585.66010519063274842 1077.85274703017853426, -8539.14477124203403946 980.40020219938992341, -8448.83680212594299519 992.53157629351017022, -8371.72278385215759045 992.79617238045739214, -8330.01122469724941766 944.24635058253215902, -8288.29966554234306386 1074.00471884350781693, -8246.58810638743671007 1097.9998183099301059, -8158.77297169328994642 957.42325031219525044, -8114.86540434621747409 961.47050465925531171, -8083.7932343457978277 1014.67044796337768275, -8052.72106434537636233 1101.38930955972909942, -8021.64889434495671594 1094.16542912209706628, -7970.75860873688179709 1049.26545086594887835, -7945.31346593284524715 1082.293828025327457, -7859.57164337008725852 1034.91745219633185116, -7816.34187200823180319 1061.03491700222571126, -7729.88232928451725456 1074.13467771896966951, -7685.3275237309098884 1051.58118531575837551, -7640.77271817730070325 965.44160099665327834, -7596.21791262369242759 1050.45470968650988652, -7478.05271343310596421 1006.06777464646756926, -7402.72848321448145725 1022.15510431882489684, -7365.06636810516829428 966.15173373694960901, -7310.57315035243118473 994.04970163105917891, -7285.24073345365286514 1101.99012243973629666, -7234.57589965609440696 973.17583221760924062, -7201.89260243045464449 965.1527344450196324, -7169.20930520481670101 961.30601884042039273, -7136.52600797917693853 1142.34496712276245489, -6990.32334774250921328 1098.93204520100834998, -6870.24288449210689578 1068.82861113028184263, -6822.61562981990027765 1151.00239521182766111, -6774.98837514769547852 1125.64807043914129281, -6727.36112047548886039 1174.22350406234545517, -6670.81895341677773104 1026.35434452381127812, -6642.54786988742125686 1075.88259000499192553, -6623.38895548756772769 1002.49690317432714437, -6585.07112668786248832 1112.54383229204313466, -6555.02819522428762866 1099.46083288166028069, -6494.94233229714154731 1156.93201070358873039, -6448.09259065180594916 1132.53558286427801249, -6354.39310736113293387 1036.11099194902772069, -6269.49275862079412036 976.79788175869043698, -6249.17980520423952839 950.5044603872247535, -6228.86685178768675542 1085.16828479001560481, -6208.55389837113216345 960.66761471244672066, -6156.64008178985750419 960.96066618256600123, -6130.68317349921926507 1166.13136511622974467, -6104.44305778184934752 1120.03913995823722871, -6078.20294206448124896 981.31882516413952544, -6051.96282634711133142 1096.21831276538682687, -6032.22559303719935997 1003.35938990370232204, -5992.75112641737723607 988.89912350241934291, -5963.56129842699374421 1008.35548716364201027, -5934.37147043661389034 1048.80933806715484025, -5905.18164244623221748 1178.93182110047428068, -5857.94105201911952463 1042.35108065905046715, -5763.45987116489413893 1175.79013021386390392, -5636.00669180900877109 989.42866143454239136, -5512.20829203192806744 960.14652443612158095, -5434.07978734291646106 983.63280340826077008, -5395.01553499841247685 1035.78996815977029655, -5336.32973052921806811 991.82431583296329336, -5306.98682829462086374 1088.91213342793389529, -5216.06897246513472055 1139.82729584571620762, -5189.13621661715478695 1090.7415487435077921, -5135.27070492119673872 1135.17989289644629025, -5092.14704473049096123 991.61021170408002945, -5070.58521463513716299 941.93320217014297668, -5004.69887850339364377 1087.41551538640146646, -4987.59424192431106349 903.47032552558584939, -4970.48960534523030219 925.97587551282367713, -4953.3849687661495409 1060.39582527601533002, -4909.88352115110319573 1028.18745718449281412, -4866.38207353605685057 889.47377448575718972, -4822.88062592101050541 920.68804204491198107, -4805.03574123820726527 931.98986624602230222, -4787.19085655540584412 888.78585948370619008, -4769.34597187260442297 1036.71524352116875889, -4735.30042222765223414 919.41886856294513564, -4667.2093229377460375 898.22593714033018841, -4619.98628231322436477 950.76739565262937504, -4572.76324168870451103 1075.85250036293291487, -4525.54020106418283831 1019.13788033879177419, -4444.1883997605436889 901.6403601507172425, -4403.51249910872502369 899.67058559773397519, -4289.14206000593003409 938.94566648700993028, -4226.81240827483452449 1055.09105614692180097, -4195.64758240928676969 938.92882133848843296, -4171.41497609292855486 1050.08914391714870362, -4147.18236977656852105 1017.7966439671936314, -4122.94976346020848723 1053.2193002110557245, -4089.42344550834604888 992.96152604016310761, -4022.37080960462117218 1080.45030316584961838, -3995.97330718330886157 1085.1483640323160671, -3943.17830234068787831 1018.58660310995901455, -3890.76973153837388963 972.34118685782777902, -3854.80091863794950768 1031.01566653758345637, -3818.83210573752694472 1066.49010498448342332, -3782.86329283710256277 1071.77060868422017847, -3744.60540617564038257 948.11050650947572649, -3725.47646284491020197 1041.98454531301422321, -3695.41902071816912212 993.31768283497262928, -3665.36157859142986126 1117.96438269216127992, -3635.30413646468878142 1174.5146846837224075, -3540.60159146300247812 1016.80702750217187713, -3493.25031896215841698 1108.78814889272598521, -3449.59754281308960344 1054.08156743633867336, -3427.77115473855519667 1087.7545452446802301, -3378.30510161251731915 1018.85696977187535595, -3279.37299536043974513 1059.87919444302451666, -3232.88278878123855975 1150.94422019740613905, -3139.90237562283800798 1008.77543567910538513, -3083.80320259538893879 966.00040847303012015, -3055.7536160816634947 1047.45044483939909696, -3022.05964340061291296 1038.47700021173932328, -3005.21265706008853158 1117.65434299037315213, -2971.05978930434866925 959.43628779006394325, -2936.90692154860880692 969.90052399133492145, -2902.75405379286894458 1085.71744497279746611, -2871.9123403037629032 1066.95863175873955697, -2841.07062681465686182 1014.83918207160400016, -2810.22891332555082045 1089.77708054438562613, -2783.86562418330504443 1016.00447434769625943, -2757.50233504105926841 1129.39585063592585357, -2731.13904589881349239 1002.69289217787400048, -2635.03794375080542522 1127.8128374823336344, -2587.45427644033225079 1102.71368475175495405, -2539.87060912985725736 911.76617501005625854, -2492.28694181938408292 1026.66618562679468596, -2389.22358748337865109 1106.68072819268263629, -2286.07628566863422748 974.8447498162422562, -2158.56982984341266274 943.68759963395814339, -2118.59442824291909346 905.80461987756234521, -2098.60672744267139933 929.1808969244148102, -2003.82634551908631693 1109.99446249023230848, -1976.60366353443350818 1002.31789178938242912, -1922.15829956512607168 1115.12683533042945783, -1874.42997247859057097 1062.64552633529342529, -1826.70164539205688925 1094.64148086156865247, -1778.97331830552138854 1064.07074700499629216, -1749.23920223079221614 1082.03827193053461997, -1719.50508615606486273 959.4570742102823715, -1689.77097008133569034 948.78242377136075447, -1645.64243908605749311 1068.80746118273691536, -1557.38537709549927968 1112.32599593695158546, -1528.84984184953827935 1035.28321916211234566, -1471.77877135761809768 1006.18657685275911717, -1393.71190671150907292 1107.07731650930645628, -1317.25648689263834967 985.76926885864577343, -1235.92996197916909296 1057.14088773936146026, -1170.89676541536937293 1027.32408230446844755, -1138.38016713346951292 1063.5553743121511161, -1039.64784036218952679 1093.20386428396932388, -990.28167697655953816 1150.11684652265489603, -911.74169724383864377 1135.77463263469780941, -863.92419543002870341 1043.45741793423030686, -816.10669361621876305 1155.42215073401553127, -768.2891918024088227 1126.88048015226559073, -740.01983774937980343 1144.50556113109450962, -683.48112964332904085 1117.30031202692271108, -605.95203161529934732 1060.78557331837305355, -581.61498053581817658 1031.36581368159477279, -532.94087837686856801 1098.13670531249385931, -383.56791837403943646 1040.70110324786355704, -321.903778363359379 1096.97043924984791374, -278.79517585303801752 1044.77111101264949866, -257.24087459787915577 970.74156202819267492, -219.97148140353965573 1043.01717936178329182, -145.43269501486975059 1032.99960242237989405, -82.42143393582955468 955.51194336555749942, 29.89309544259049289 1166.63026191688027211, 124.90989255712156591 1135.58214703278031266, 216.30827952954132343 1111.72027728962075344, 285.19890020332059066 1079.42711095490130901, 319.64421054021113378 1022.75049056925490731, 367.78655180910027411 1100.28085724120319355, 415.92889307799123344 1138.10288522906193975, 464.07123434688037378 1061.67471303558522777, 521.95535618049143523 1186.39445403986337624, 570.49836314342064725 1139.03975155881630599, 667.5843770692608814 1017.22464775228286271, 698.69577157487037766 992.13448931042830736, 729.80716608049078786 1104.4629503158987518, 760.91856058610028413 1026.05263411263558737, 823.97719627088190464 1140.65063744454278094, 855.5065141132708959 1080.29527178762009498, 873.12290306736031198 1146.1544537549875713, 890.73929202145154704 1110.41131720713065079, 908.35568097554096312 1038.47669005298030243, 1006.92263931876186689 1100.69503999724520327, 1099.33948705732109374 1014.16062744991495492, 1145.54791092660161667 1109.58021440744141728, 1265.86757359255170741 1060.58957617544933782, 1295.95196928288169147 942.8248306218961261, 1326.03636497321167553 914.95069775560341441, 1356.1207606635416596 1072.1495368288908594, 1399.62810081257157435 938.27636689779137669, 1486.64278111061139498 976.56711924285582427, 1534.94612604906069464 1029.76786362754319271, 1559.09779851828170649 1077.43603414216022429, 1653.55903277288052777 945.33279041900618722, 1747.95335038553093909 950.79471131675518336, 1780.86946942142094485 914.10354277173405535, 1846.70170749321187031 1001.34449101940822402, 1874.59068315498188895 947.17772817688523901, 1902.47965881675190758 1028.64473768891730288, 1930.36863447852192621 1000.12830562888939312, 1953.82732215452051605 1038.86269162970938851, 2000.74469750652133371 1036.97872849111763571, 2091.32502055021177512 990.20919560580659891, 2136.61518207205153885 939.17114700764295776, 2161.87026150139172387 959.90798978445081957, 2212.38042036005026603 1011.34717015001206164, 2270.6232267514205887 948.8958203735405732, 2299.74462994710120256 987.0436986178508505, 2375.23134226513138856 1051.58925044471766341, 2410.52438295880165242 1019.42023385958668769, 2481.11046434616037004 1017.04902651525344481, 2552.66813770448061405 1009.76887930798284287, 2598.02009248624199245 960.83785169578186469, 2620.69606987712177215 954.09937674887260073, 2723.06661887095106067 1045.52848082089030868, 2800.22316857566147519 1021.47435543183109985, 2838.80144342802122992 920.4515334004122451, 2877.84826925849120016 978.13304553655007112, 2955.94192091945114953 981.98228145788243637, 2973.20424825340160169 996.36246466967008928, 3007.72890292129159207 1011.92352999730746888, 3052.4352848893704504 1069.93557080462323938, 3097.14166685745112773 987.33125066885259002, 3141.84804882553180505 1081.04998294587335295, 3200.14833511435062974 951.33755085001325824, 3229.29847825877186551 1045.32499266289073603, 3263.86676888930196583 910.70301467376862092, 3281.15091420456155902 1051.19794001448735798, 3309.14559004353031924 984.89086236165348964, 3337.14026588251181238 949.11022190455923919, 3365.1349417214805726 1022.25201407769282014, 3505.31779331672078115 948.86173541308789936, 3547.93224777698196704 906.69182961999194958, 3590.54670223725042888 1045.58774784188676676, 3633.16115669752070971 942.9381768311363885, 3679.66277367234033591 976.62178127261722693, 3726.16439064717087604 997.68535003022543606, 3772.66600762200141617 1007.42286038723705133, 3818.73639352806094394 948.09162339972499467, 3910.87716534018181846 946.14675636634410694, 3931.67942210239198175 1022.14776574442907986, 3973.28393562682140328 991.87016202229597184, 4013.93148167414074123 1048.85644738220867112, 4095.22657376878123614 990.53190513592835487, 4138.45172519572042802 1040.64868588881404321, 4181.67687662265052495 1039.76914587011992808, 4224.90202804959153582 937.11934506140164558, 4265.364729905850254 1040.79962973914098257, 4346.29013361838042329 943.59589462290705342, 4381.04610790644073859 942.80515236558676406, 4398.4240950504608918 1016.00189148804702199, 4429.65557507048106345 1009.81980307111598449, 4460.88705509051033005 986.86471483336504207, 4492.1185351105305017 931.38996270713278136, 4514.35731201338057872 939.58393709829169893, 4536.59608891624156968 973.87701976381731583, 4558.83486581910074165 925.08711755832678136, 4606.98532938166135864 1093.99147677252267385, 4703.28625650679168757 949.23199187780937791, 4781.5362296094699559 998.77461992195230778, 4820.66121616081181855 1029.79476348073330882, 4839.98075464274188562 962.77691514343769086, 4859.30029312468286662 1043.73982490627395237, 4878.61983160662020964 1011.98120400747893655, 4981.25928661744001147 926.56063244653319089, 5017.81842951366161287 925.93842458502422232, 5036.09800096177241358 1022.29609763722100979, 5098.39449275468177802 1002.42148387965858092, 5129.54273865114191722 946.04788466650506962, 5204.24797929635133187 1019.37729488134891653, 5231.2142853382119938 1042.87361999034646942, 5285.14689742192967969 1101.5640952620783537, 5358.7202194884794153 1116.89960804880547585, 5401.40957968326074479 993.25276850248746996, 5444.09893987803116033 939.38063900168526743, 5486.78830007281248982 969.37724520723531896, 5551.98773510263163189 1154.59753052254563954, 5590.93809901565145992 962.10854371220875692, 5668.83882684170202992 1142.95940846461940055, 5761.15747171220027667 1007.87960822538229877, 5807.31679414745121903 1089.08929538157326533, 5870.47751620118106075 1172.63940918465164032, 5941.43468985794061155 1066.12869359150590753, 5976.91327668632038694 1023.68441236623812074, 6030.74720655242163048 1088.39980173043636569, 6057.66417148547225224 1088.52515608867247465, 6176.09348568976020033 1031.22554097272472973, 6281.50329010141103936 984.72567971222133565, 6309.11978481042933709 1029.45065803837019303, 6336.73627951945127279 1100.94552372319299138, 6364.35277422846957052 1043.36664159355314041, 6434.84953442221194564 1031.54280963812789196, 6470.09791451907040027 998.72278635001657676, 6527.22924906839216419 1154.57411384760484907, 6610.59159162561081757 1182.47818627318224571, 6644.7897996915398835 1024.12215769398289922, 6661.88890372451169242 1097.71648262974258614, 6702.68675640508263314 1212.25738899742691501, 6784.2824617662208766 1093.00477442982446519, 6805.35443600257167418 1217.58374507174653445, 6826.42641023892974772 1179.00956473927340085, 6847.4983844752805453 1184.53460533425732137, 6873.5837052794322517 1213.16710439190546822, 6899.66902608359123406 1221.74695434303521324, 6925.75434688775021641 1231.26974452726904019, 6967.73937566609129135 1197.62290967214880766, 7009.72440444443236629 1167.72910992927450025, 7051.70943322276980325 1219.61619014553343732, 7147.28611750147138082 1236.50014290232161329, 7195.07445964082035061 1272.5487450524774431, 7234.80078481340206054 1306.92519156856269547, 7274.52710998598013248 1282.05736023240160648, 7314.25343515855092846 1190.53851995797822383, 7418.76186791583131708 1239.51857655240610256, 7455.79805228778241144 1325.96566595417993994, 7492.83423665974078176 1296.565330106841202, 7529.87042103170279006 1235.22254295153379644, 7586.36083252753996931 1342.70111585170729995, 7614.60603827544946398 1305.8445328334369151, 7713.54893720300060522 1336.99974224790912558, 7763.02038666678163281 1165.24117135040341964, 7827.25208254561039212 1243.8707971458686643, 7859.36793048503204773 1336.21661870188881949, 7883.75397282550147793 1188.91673323316695132, 7932.52605750644033833 1275.72216622483119863, 8045.13182980008241429 1225.84990367073305606, 8065.69994368383231631 1328.99543734923463489, 8086.26805756758949428 1229.69473906766825166, 8106.83617145135031024 1181.0297205489780481, 8134.86692865248005546 1126.86369796060284898, 8162.89768585360980069 1305.79797710740513139, 8190.92844305475045985 1241.72064015356136224, 8236.02986789968235826 1230.83028116886930547, 8258.58058032215012645 1255.93278551589628478, 8366.49246573862001242 1326.36439583132641928, 8412.63840956836975238 1165.86267086003294935, 8504.93029722787287028 1161.79333828927701688, 8524.62753482718289888 1303.04474186751303932, 8564.0220100257993181 1215.92808604684887541, 8618.72626056915214576 1289.46856915238777219, 8681.91619591499147646 1261.74792219271148497, 8713.51116358790932281 1229.42458611483129971, 8800.20110047868183756 1210.64955787508461071, 8843.54606892406991392 1267.31097295576410033, 8965.19233231480211543 1246.59686048185517393, 8995.13344451618286257 1204.55617942112371566, 9025.07455671755997173 1235.89142497200055004, 9055.01566891892980493 1216.76578935034808637, 9155.17771867022202059 1126.06182713446605703, 9224.55513261345004139 1076.37246852265025154, 9513.70740542743260448 1003.74978724602465263, 9373.99411753010099346 817.40467122658151311, 9189.86642564183239301 762.12172765771424565, 9155.17771867022202059 710.516773972648366, 9121.79036875311976473 826.65978341541040209, 9088.40301883603206079 675.91223865031315654, 9055.01566891892980493 692.98932028533340599, 8965.19233231480211543 848.96335890173145344, 8924.64357785122956557 713.03488403170524634, 8884.09482338764973974 856.38384556627852362, 8843.54606892406991392 749.50010980947308781, 8756.85613203330103715 792.89614644562379908, 8713.51116358790932281 813.10719476538452, 8650.32122824206999212 724.6161092416206202, 8618.72626056915214576 764.16504424652703165, 8600.49151038803211122 858.49244194006598718, 8582.25676020691935264 875.45920849802052999, 8564.0220100257993181 773.52344781038198107, 8544.3247724264892895 871.24561879450129709, 8504.93029722787287028 879.23173341412348236, 8458.78435339811949234 753.21696946566646602, 8366.49246573862001242 755.81718757847772849, 8330.5218372664621711 768.05352795936994426, 8294.55120879431160574 839.4097997366313848, 8258.58058032215012645 774.76490223934331425, 8213.47915547721095209 805.27265561045965114, 8190.92844305475045985 867.94719624711854067, 8106.83617145135031024 847.1204739811704485, 8045.13182980008241429 755.68766667999273068, 8007.59657236886232567 904.10307018462663109, 7970.06131493764951301 715.02749586273387195, 7932.52605750644033833 837.03456934025246028, 7908.14001516597090813 886.6473319992519464, 7859.36793048503204773 905.64720910927894693, 7795.13623460619237449 853.18422274791043947, 7763.02038666678163281 842.16094385034136849, 7664.07748773923049157 888.38194013817928862, 7614.60603827544946398 912.64328937850086731, 7558.11562677961228474 887.49514547826038324, 7529.87042103170279006 912.29714260842615658, 7418.76186791583131708 796.88589272983642786, 7383.92572366340209555 927.4123171327437376, 7349.08957941098014999 838.25376731585993184, 7314.25343515855092846 918.98383585271949414, 7195.07445964082035061 902.32934905384706781, 7099.49777536212241102 894.37831500055881406, 7051.70943322276980325 761.76577511694949862, 6925.75434688775021641 774.05473333889415244, 6847.4983844752805453 710.81167311866272485, 6784.2824617662208766 659.5402035116726438, 6743.48460908564993588 804.34021000153393288, 6661.88890372451169242 656.67954549653552476, 6627.69069565857171256 652.35530855887589041, 6610.59159162561081757 737.4261406032501327, 6582.80414410653065715 641.44393089450318257, 6555.01669658746141067 612.51757774698626235, 6527.22924906839216419 597.34754739053755657, 6508.18547088528976019 764.06610465706762625, 6489.14169270218008023 615.8845185363136352, 6470.09791451907040027 639.23361352134679692, 6399.60115432534257707 683.76406537821026177, 6364.35277422846957052 692.29179303344903929, 6281.50329010141103936 738.69967825022024499, 6246.36668863086197234 753.04328917277985056, 6211.23008716031290533 687.20385112204542111, 6176.09348568976020033 569.87138265543330817, 6136.61704762167028093 583.77343965669820136, 6097.14060955356217164 669.84965420109551815, 6057.66417148547225224 730.87891644765329602, 6003.83024161937100871 620.12702885165765565, 5976.91327668632038694 561.2110364486193248, 5905.95610302956083615 630.74939219550333291, 5870.47751620118106075 739.82242413585436225, 5849.42394218326990085 754.69413714922347935, 5828.37036816536237893 734.35802115167530246, 5807.31679414745121903 691.98306622362611051, 5714.99814927694933431 681.94591508397707003, 5668.83882684170202992 742.08722597835799206, 5629.88846292868220189 622.73183340920274986, 5551.98773510263163189 581.30580991996066587, 5530.25459009269070521 702.42020585051704984, 5508.52144508274977852 663.41570475822186381, 5486.78830007281248982 631.40715934580862267, 5358.7202194884794153 551.84233225136040346, 5334.19577879963071609 631.99086214021986052, 5309.67133811078201688 619.40774395346898018, 5285.14689742192967969 597.58576026076332255, 5258.18059138007265574 529.49237606396786759, 5204.24797929635133187 540.97988627110476045, 5179.34623241462213628 547.63392513651319859, 5154.44448553288202675 628.15464453326410421, 5129.54273865114191722 581.17630108022649438, 5067.24624685822163883 506.61560603696523231, 5036.09800096177241358 595.25455639055132906, 4999.53885806555081217 610.88295847296649299, 4981.25928661744001147 580.19879550764301257, 4947.04613494716068089 621.31208605522556354, 4912.83298327689226426 657.99737900942318447, 4878.61983160662020964 606.97041579512722365, 4820.66121616081181855 626.24644426611837389, 4742.41124305813173123 632.37362463078557084, 4703.28625650679168757 638.37993913205309582, 4655.13579294422197563 670.03998181040674353, 4558.83486581910074165 529.96357206055085953, 4492.1185351105305017 512.73576309881650559, 4398.4240950504608918 660.94571563937495284, 4363.66812076241149043 675.95202384928256834, 4346.29013361838042329 569.62773650167150663, 4305.82743176212170511 660.51864120314257889, 4224.90202804959153582 502.99619507908369087, 4095.22657376878123614 579.69125244781525907, 4054.57902772146189818 452.04687891185471926, 3973.28393562682140328 579.38779473601698555, 3952.48167886460032605 554.63235142273811107, 3910.87716534018181846 461.05371063643735852, 3864.80677943412047171 583.21678916770542855, 3772.66600762200141617 650.18511729202305105, 3633.16115669752070971 573.05138473204237926, 3505.31779331672078115 577.34808669677386206, 3458.59017611831040995 519.10240677239266915, 3411.8625589198909438 629.21002154997881917, 3365.1349417214805726 598.66144394948946683, 3281.15091420456155902 530.47233421075475235, 3246.5826235740314587 558.85785421912510174, 3229.29847825877186551 599.23471672600521742, 3170.9981919699403079 517.07934309408960871, 3141.84804882553180505 536.09989238104503784, 3007.72890292129159207 651.45310290607790193, 2990.46657558734113991 517.31298674776314783, 2955.94192091945114953 651.65003255908072788, 2916.89509508897026535 658.75932848578395351, 2838.80144342802122992 601.06309127657334557, 2761.6448937233108154 569.25952808331271626, 2723.06661887095106067 555.28853609181601314, 2688.94310253968069446 547.75411076181410408, 2654.81958620840123331 662.26489672702780354, 2620.69606987712177215 572.2006602176177239, 2575.34411509536039375 602.02496451260117283, 2552.66813770448061405 479.76952509665215985, 2528.81557991838053567 648.70791291565876691, 2504.96302213227136235 602.36755821885481055, 2481.11046434616037004 557.08634049181580394, 2445.81742365248101123 674.08944905920907331, 2375.23134226513138856 524.0719384720873677, 2350.0691048257813236 615.29933107359966016, 2324.90686738644035358 667.23627768253481918, 2299.74462994710120256 631.51290189603514591, 2241.50182355573087989 464.87082184514429173, 2212.38042036005026603 455.68457802188072492, 2187.12534093072099495 543.49581076458605366, 2136.61518207205153885 596.32360218441090183, 2046.03485902837019239 611.94064044695380744, 2000.74469750652133371 633.30333576938267015, 1977.28600983052092488 641.80958926970220091, 1930.36863447852192621 554.09769668296917189, 1846.70170749321187031 650.72223486947791571, 1813.78558845732186455 547.9685661585044727, 1747.95335038553093909 600.24080209413159537, 1716.48857784798019566 503.37028500486405846, 1685.02380531043127121 519.24767617809732201, 1653.55903277288052777 520.76976165456767376, 1622.07195468802092364 525.50367063484873142, 1590.58487660315040557 709.35477086591924945, 1559.09779851828170649 598.82742573615269066, 1510.79445357983058784 554.96476249468355491, 1486.64278111061139498 566.30531355162020191, 1443.13544096159057517 660.5069378467730985, 1356.1207606635416596 493.92897854154705328, 1265.86757359255170741 645.25603404881701408, 1225.76101937057137548 563.92830414163518071, 1185.6544651485819486 553.97198387269736486, 1145.54791092660161667 628.00941875864918984, 1053.13106318804057082 639.49000543753061265, 1006.92263931876186689 701.9005302264367856, 974.06698653768035001 697.30667014444907181, 941.21133375661156606 638.25843837673767212, 908.35568097554096312 750.05867788376122007, 855.5065141132708959 560.42916067779572131, 792.44787842849109438 660.86110387821258882, 760.91856058610028413 634.82091292146697015, 667.5843770692608814 772.25449766943722807, 619.04137010634076432 783.5258494272960661, 521.95535618049143523 721.59687315293149368, 502.66064890262168774 622.35453109495745139, 483.36594162475194025 720.62980454142621056, 464.07123434688037378 672.52030665906340801, 319.64421054021113378 682.68698719064559555, 250.75358986643186654 739.11507315615449443, 216.30827952954132343 587.70462848237650633, 185.84215053873049328 567.84769702729818164, 155.37602154793057707 617.63273636514861664, 124.90989255712156591 562.23141611689413821, 93.23762685227120528 705.90199289005386163, 61.56536114743175858 739.64222731568588642, 29.89309544259049289 587.5332899942354743, -7.54508101687861199 589.31197637394370759, -44.98325747635863081 643.83018933956930141, -82.42143393582955468 726.00621241479723267, -103.42518762883810268 676.92401538326714672, -124.42894132185938361 700.44335416102273939, -145.43269501486975059 603.98189889629816207, -182.7020882091983367 553.13245865572480398, -257.24087459787915577 653.76836296945725735, -300.34947710819869826 588.33191280109224408, -321.903778363359379 567.47369762998755505, -342.45849170024848718 549.47615759804500613, -363.01320503713941434 654.4106315731136192, -383.56791837403943646 694.84296668328215674, -433.35890504164854065 577.44822791502781456, -483.14989170925946382 623.12018627065185683, -532.94087837686856801 679.78378782827792293, -557.27792945634973876 573.807672197362308, -605.95203161529934732 586.75174194490659829, -631.79506429130924516 704.03663662952192226, -657.638096967319143 752.60429635558489281, -683.48112964332904085 753.37958097769330834, -711.75048369635806012 625.73969969820677761, -768.2891918024088227 742.67780205233930246, -911.74169724383864377 743.43675417980580278, -937.92169048807954823 649.59076125385024625, -964.1016837323186337 714.99672356835799292, -990.28167697655953816 609.88895184398325, -1089.01400374782861036 716.05690655167325076, -1138.38016713346951292 686.33412425323558637, -1203.41336369726923294 745.95389910835888259, -1235.92996197916909296 755.67501646874779908, -1263.03880361698975321 626.40414869065989478, -1290.14764525481950841 577.60537124821485122, -1317.25648689263834967 543.91907403259631337, -1342.74162683225949877 553.95470333607852353, -1368.22676677188974281 675.79191520926929115, -1393.71190671150907292 692.75441109223095282, -1419.73419492687935417 715.40245714360116835, -1445.75648314224963542 536.53205833635354338, -1471.77877135761809768 526.47924557160035874, -1500.31430660357909801 695.28667074548081928, -1557.38537709549927968 703.06307870086277489, -1601.51390809077929589 699.73757987165663508, -1689.77097008133569034 599.2409257325047065, -1778.97331830552138854 598.24697562700089293, -1922.15829956512607168 584.79959329901225829, -1949.38098154977888044 670.3519265920667749, -2003.82634551908631693 703.63806722838944552, -2035.41980616028195072 626.88823662181107466, -2067.01326680147576553 571.29204931294395919, -2098.60672744267139933 691.3699348444969246, -2138.58212904316496861 623.11191805447276693, -2158.56982984341266274 522.64207980526532538, -2201.07198178515318432 643.82905270802393716, -2243.5741337268937059 696.65006362125336636, -2286.07628566863422748 599.58351474988205609, -2320.45871960688236868 660.7365624894996472, -2354.84115354513050988 573.16030619762705101, -2389.22358748337865109 540.85296975087635474, -2423.57803892871379503 599.98772785180995015, -2457.93249037404893897 594.51466518624056334, -2492.28694181938408292 653.63388057875226878, -2635.03794375080542522 533.07170437610898261, -2667.07164446680872061 567.8568167767596151, -2699.105345182810197 621.03707391282944172, -2731.13904589881349239 715.86573201622911711, -2810.22891332555082045 577.88399508601787602, -2902.75405379286894458 547.31423256513573961, -3005.21265706008853158 550.02868391638730827, -3038.90662974113911332 666.47809842996139196, -3055.7536160816634947 627.28769057750810134, -3111.85278910911256389 627.05972705872886763, -3139.90237562283800798 614.40076156659824846, -3186.39258220203919336 752.89505601769735676, -3279.37299536043974513 620.5604307847356722, -3328.83904848647762265 595.84530563920031909, -3427.77115473855519667 720.8490035618052616, -3471.42393088762401021 591.02055632084648096, -3493.25031896215841698 763.63068966105038271, -3587.95286396384472027 643.6772926904848191, -3635.30413646468878142 651.18328861192219392, -3725.47646284491020197 574.17547428047100766, -3763.73434950637238217 539.83704870906126416, -3782.86329283710256277 650.70762665122356339, -3890.76973153837388963 626.72043645268809087, -3908.23925513914400653 586.59265406299050483, -3925.70877873991594242 701.50957993249483025, -3943.17830234068787831 542.24917349495331109, -3969.57580476199836994 651.43146578020775905, -4022.37080960462117218 610.47713282888685171, -4055.89712755648361053 685.9185688292376426, -4122.94976346020848723 518.3974817527544019, -4195.64758240928676969 561.6422243219185475, -4257.97723414038227929 591.72216777077301231, -4289.14206000593003409 582.51398652933823996, -4327.26553970686109096 655.73621889295930032, -4365.38901940779396682 654.40964284886410951, -4403.51249910872502369 522.12276234630576255, -4484.86430041236235411 658.47251007913416743, -4525.54020106418283831 590.38305744531760411, -4667.2093229377460375 575.97917738173487123, -4701.25487258269822632 479.60767128006818893, -4769.34597187260442297 658.55063381222305452, -4822.88062592101050541 610.20859621304941811, -4953.3849687661495409 582.98335149993249615, -5004.69887850339364377 676.06860780788292686, -5026.6609905473087565 547.63038318874885135, -5048.62310259122205025 605.30097844789213468, -5070.58521463513716299 665.25272955943569286, -5113.70887482584475947 612.86480248715395192, -5135.27070492119673872 692.77698291938918373, -5162.20346076917667233 724.52368955988299604, -5216.06897246513472055 742.2756694531121866, -5246.37492440829555562 689.26629472195884318, -5276.68087635145820968 615.61212630871455076, -5306.98682829462086374 592.83942421193421524, -5365.67263276381527248 577.64847069908864796, -5395.01553499841247685 688.99042796378876119, -5473.14403968742408324 555.90574283684145485, -5512.20829203192806744 724.34532426216912882, -5553.47442529095496866 629.14065193616738725, -5594.74055854998186987 651.09480949577744013, -5636.00669180900877109 661.59042629039549865, -5678.49108492763662071 645.79449464113145041, -5720.97547804626447032 696.36693563015285235, -5763.45987116489413893 647.38465191587170011, -5810.70046159200683178 641.64576792271327577, -5905.18164244623221748 569.90537934059614145, -5992.75112641737723607 635.32496468763326902, -6012.48835972728738852 584.87760910172710282, -6051.96282634711133142 689.88064120801709578, -6130.68317349921926507 637.22530670708579237, -6182.59699008049392432 650.26977567459391594, -6208.55389837113216345 728.77552125500903912, -6269.49275862079412036 685.35447943472479437, -6297.79287486757311854 538.59968338073190353, -6326.0929911143539357 664.00307055852624671, -6354.39310736113293387 603.22578063070841381, -6401.24284900646853202 664.094191980803771, -6494.94233229714154731 576.83273256371035131, -6524.98526376071458799 754.33729118527264745, -6585.07112668786248832 582.06738345919939093, -6604.23004108771419851 619.21925176903550891, -6642.54786988742125686 669.71730205986523288, -6699.09003694613238622 623.58882320595682813, -6727.36112047548886039 617.21756052444311536, -6870.24288449210689578 572.52385365038435339, -6910.26970557557433494 590.67895882358629933, -6950.29652665904177411 566.96949068603930755, -6990.32334774250921328 630.58633650609601773, -7039.05756782139906136 599.12126862364061708, -7087.79178790028709045 597.78714551702682911, -7136.52600797917693853 702.98737536266014558, -7234.57589965609440696 695.40965369922821537, -7259.90831655487272656 646.67730498837249797, -7310.57315035243118473 698.66184421733873933, -7328.73755627001082757 613.10177408504546293, -7346.90196218759047042 692.179584632304568, -7365.06636810516829428 709.14728623856740342, -7440.39059832379280124 709.15389510073646306, -7478.05271343310596421 698.17558070076256627, -7517.441113163301452 734.81668089700747259, -7556.8295128934969398 625.54816420571251001, -7596.21791262369242759 718.98439096424522177, -7729.88232928451725456 684.10339736335299676, -7773.11210064637452888 649.70879399726686643, -7859.57164337008725852 532.88903128190827374, -7888.15225089100749756 561.53915828810841049, -7916.73285841192591761 584.05863488673594475, -7945.31346593284524715 532.4023275999852558, -7996.20375154091925651 622.28636875562278874, -8021.64889434495671594 662.9787975563258442, -8114.86540434621747409 504.36892898834230436, -8202.68053904036423774 726.6254664245125241, -8246.58810638743671007 519.05964688046310584, -8371.72278385215759045 557.24789390208638906, -8397.42745661008666502 626.31047029066689902, -8423.13212936801392061 587.01305263539597945, -8448.83680212594299519 581.28101878418954129, -8478.93945849797273695 705.15742406848767132, -8509.0421148700042977 623.12816462678620155, -8539.14477124203403946 615.07297641522404774, -8678.69077308783016633 704.67701265306857294, -8734.31895414974678715 598.97525842073878266, -8803.59634450307385123 614.40521111346595262, -8838.23503967973738327 807.07777240583129696, -8864.17599234916815476 728.85231563321474368, -8916.05789768802787876 806.91556875394769577, -9064.0171658052404382 675.16822486079524879, -9108.40722390074006398 734.02798260154668242, -9197.18734009173749655 756.03293525051117285, -9288.23128663816896733 641.28583980992482338, -9329.22412234771945805 646.03382905995022156, -9411.2097937668186205 800.33807053269777043, -9459.50487052710923308 664.36649650961135194, -9507.79994728739984566 671.48679313238801569, -9556.09502404769045825 647.82029539077859681, -9610.45110427087638527 650.33676835824769569, -9648.07999832687892194 750.79951483685056246, -9723.33778643888581428 677.59890178247474068, -9767.93123294561337389 761.26240004942496853, -9857.11812595907213108 690.45172017837694511, -9905.86159509707613324 643.16475709640496916, -9954.6050642350801354 815.81170992287582067, -10003.34853337308413757 805.19174243189695517, -10049.56053808267097338 787.66553866796164129, -10095.7725427922578092 682.5931604586502317, -10141.98454750184464501 664.27534651596727144, -10183.93636990023696853 688.47377359060237723, -10225.88819229862929205 737.35269979965778475, -10267.84001469701979659 751.50886908035977285, -10397.82060783809356508 619.79002433228606606, -10417.89178138449460675 665.28871053905152166, -10458.03412847729669011 814.41746376285664155, -10493.93093400908219337 804.25855187074353125, -10565.72454507265138091 761.08066880234900964, -10624.66909496483094699 822.75143893252015914, -10654.14136991091982054 628.0444914794967417, -10681.30157739835703978 764.21022863556117954, -10708.46178488579425903 690.21977129784318095, -10735.62199237323147827 763.67376145539799381, -10807.03674255008991167 706.95159739359974083, -10826.48467634721237118 795.33852180798135123, -10865.3805439414572902 715.72166823404404568, -10921.85130510217459232 713.17012494313121351, -10950.08668568253415287 631.26692781098279283, -11040.53925289185281144 670.52107005641369142, -11089.86970734093301871 732.92529873046669309, -11139.20016179001322598 778.32638695371622362, -11188.53061623909343325 689.69593140286053767, -11252.87104693022047286 704.05584983572191504, -11285.04126227578490216 589.08752412774470031, -11328.95339922557468526 647.90306514082999456, -11416.77767312515788944 587.09805465892554821, -11556.58527979027167021 692.90621421302603267, -11695.5972439257257065 633.8032691447730258, -11637.61616249147482449 1091.42775211438902261))'
    q_wkt = 'Polygon ((-11163.62430071464405046 -630.21399003800638638, -11135.22082113477881649 -615.38391938328732067, -11118.01782653807094903 -590.18500260102769062, -11100.81483194136308157 -630.80713290319476982, -11054.21229638632576098 -650.30912388980118521, -11007.60976083128480241 -674.3304312855734679, -10961.00722527624748182 -634.89382897203245193, -10917.09508832645587972 -636.45045899105139142, -10829.27081442687267554 -645.71503780026318964, -10764.93038373574745492 -640.97973791362960583, -10732.76016839018120663 -574.62764723427494573, -10584.76880504294240382 -567.07140308939051465, -10554.61794930650285096 -601.84376287524719373, -10524.4670935700632981 -615.50971923285169396, -10494.31623783362374525 -594.37437517062721781, -10437.84547667290462414 -565.84174708372734131, -10409.61009609254688257 -580.51572556077076115, -10390.16216229542624205 -582.78156775531624589, -10351.26629470117950405 -537.50771507364265744, -10327.46137797556002624 -574.43707561894439095, -10303.65646124994236743 -585.52139978886111749, -10279.85154452432107064 -552.50035975920013698, -10198.3709220620112319 -602.04137404990478899, -10139.42637216982984683 -586.21832240602680031, -10109.95409722374097328 -549.36939025131982817, -10074.05729169195547001 -530.43520970623717403, -10002.26368062838810147 -544.43382148913906349, -9982.1925070819852408 -544.1443105472485513, -9942.05015998918315745 -579.08877890486678552, -9898.72329560882644728 -567.84014004416303578, -9855.39643122846973711 -607.22460807807692618, -9812.06956684810938896 -550.33995082022624956, -9686.21409965293423738 -614.4306720896177012, -9547.57808552417554893 -596.14515082204525243, -9401.34767811016172345 -543.5597233046423753, -9356.75423160343234485 -568.69511331721832903, -9267.56733858997540665 -555.08599550623534924, -9229.93844453397105099 -585.9732397575169216, -9154.68065642196597764 -600.48601105490388363, -9136.5619630142373353 -616.94084280520246466, -9118.44326960650869296 -572.4419675325557364, -9100.32457619878186961 -578.37072316511785175, -8955.43934591790821287 -577.392531121992306, -8914.44651020835954114 -534.82342969867295324, -8832.4608387892585597 -512.4848634233546818, -8802.1128566071165551 -535.92212283332833067, -8771.76487442497091251 -561.09336812163360264, -8741.41689224282890791 -567.44054168354523426, -8697.02683414732746314 -541.23973206703999494, -8608.24671795633184956 -550.54493488796947531, -8558.92696191725917743 -592.48470849760929013, -8509.60720587819014327 -587.9875017799570287, -8460.28744983911747113 -558.44547321703726084, -8434.34649716968851862 -574.42981057240058362, -8382.46459183082697564 -565.06353615720490779, -8313.18720147749991156 -591.39266620081934889, -8278.54850630083819851 -598.05708123975455237, -8260.00577928019993124 -604.49549056965588534, -8241.46305225955802598 -593.40269678648792251, -8222.9203252389197587 -604.44177633486015111, -8176.40499129032195924 -617.99133330609220138, -8129.88965734172234079 -643.13811735679928461, -8083.37432339312454133 -669.36785431241969491, -7993.06635427703258756 -680.21347147346455131, -7915.95233600324809231 -690.90492873028551912, -7874.24077684833991952 -712.68934661922708074, -7832.52921769343356573 -673.62540533402352594, -7790.81765853852630244 -643.17202307133288741, -7703.00252384438044828 -701.16502798897749926, -7659.09495649730797595 -709.04127746198651039, -7628.02278649688742007 -705.69456997153542943, -7596.95061649646686419 -655.5937404723963482, -7565.87844649604630831 -678.28216285019129828, -7514.98816088797229895 -675.07918092125510157, -7489.54301808393483952 -657.41256122898948888, -7403.80119552117776038 -684.03756327057863018, -7360.57142415932139556 -678.38447968922514519, -7274.11188143560775643 -646.90859439946416387, -7229.55707588199948077 -661.13622154252948349, -7185.00227032839029562 -695.05218119775872765, -7140.44746477478201996 -650.12945069145030175, -7022.28226558419555658 -667.05823342732833225, -6946.95803536557104962 -663.03732723171037833, -6909.29592025625879614 -683.1716636246253529, -6854.80270250352168659 -683.93877549757462475, -6829.47028560474245751 -648.51484088829238317, -6778.80545180718399934 -682.85748183428563607, -6746.12215458154514636 -679.91893901516345977, -6713.43885735590629338 -680.03639476452212875, -6680.7555601302674404 -614.81681864769825552, -6534.55289989359880565 -633.46650461897934292, -6414.47243664319648815 -642.57774799385197184, -6366.84518197099077952 -588.71034564604428851, -6319.21792729878507089 -614.39563170464475661, -6271.59067262657936226 -596.96808530884072752, -6215.04850556786732341 -671.98701958530659795, -6186.77742203851084923 -633.20418966066881694, -6167.61850763865822955 -652.15461088443407789, -6129.3006788389520807 -624.92896612428717162, -6099.25774737537813053 -649.17615492327468019, -6039.17188444823113969 -608.7475647717103584, -5992.32214280289554154 -631.44511709395828802, -5898.62265951222343574 -669.27494944039904112, -5813.72231077188371273 -692.28388397814205746, -5793.40935735533003026 -700.1612037637960384, -5773.09640393877634779 -658.35184666065174497, -5752.78345052222266531 -677.57830979110394765, -5700.86963394094709656 -688.82294330132504001, -5674.91272565030885744 -601.7872915662799187, -5648.67260993293984939 -610.90177261617395743, -5622.43249421557084133 -664.81107179439823085, -5596.19237849820183328 -615.5517894140170938, -5576.45514518828986184 -666.94337347686496287, -5536.98067856846682844 -653.6396958427590107, -5507.79085057808424608 -653.29756534176021887, -5478.60102258770348271 -634.44578103798312441, -5449.41119459732180985 -606.71808460591250878, -5402.170604170209117 -651.69939136141829295, -5307.6894233159837313 -598.78900441851692449, -5180.23624396009927295 -662.99100745983650995, -5056.43784418301856931 -687.00152574939806982, -4978.30933949400696292 -676.99009516135242848, -4939.24508714950297872 -659.75252274944614328, -4880.55928268030766048 -672.94827443617759855, -4851.21638044571045612 -630.18404938039043373, -4760.29852461622431292 -606.69161256107054214, -4733.36576876824528881 -651.57244254676606943, -4679.50025707228724059 -634.29048123918710189, -4636.3765968815805536 -701.09549588855020374, -4614.81476678622766485 -702.02861680245473508, -4548.92843065448323614 -668.21958488897462303, -4531.82379407540156535 -739.39977740887843538, -4514.71915749632080406 -740.21409009020339909, -4497.61452091723913327 -692.3626950332090928, -4454.11307330219278811 -717.8556390448845832, -4410.61162568714644294 -762.35865228663988091, -4367.11017807210009778 -748.92599626229684873, -4349.26529338929776713 -741.4103657384273447, -4331.42040870649634599 -761.26699639509774897, -4313.57552402369401534 -703.10759818683095546, -4279.52997437874182651 -752.58155874108297212, -4211.43887508883653936 -753.97706961247945401, -4164.21583446431486664 -738.08298413612237709, -4116.99279383979410341 -687.28058264467040317, -4069.76975321527243068 -708.01446421949208343, -3988.41795191163419076 -760.3994833665187798, -3947.74205125981461606 -754.95019026483078051, -3833.37161215702053596 -721.14111405195831139, -3771.04196042592502636 -692.79907152827604477, -3739.87713456037727155 -724.65193922789194403, -3715.64452824401814723 -688.62603301167064274, -3691.41192192765811342 -708.82443822553932478, -3667.1793156112989891 -675.98797227690533873, -3633.65299765943655075 -715.98088264529496882, -3566.60036175571076456 -668.40575302932097657, -3540.20285933439936343 -661.98751638922431084, -3487.40785449177747068 -680.23369548970140386, -3434.99928368946348201 -686.95494803767905978, -3399.03047078904000955 -669.19645060095513145, -3363.06165788861653709 -642.96475131195916219, -3327.09284498819306464 -656.99849541933531327, -3288.83495832672997494 -701.45720351898648914, -3269.70601499599979434 -642.06278686237965303, -3239.64857286925962399 -678.3692006087505888, -3209.59113074251945363 -634.66719843285591196, -3179.53368861577928328 -597.48836983327032613, -3084.83114361409207049 -646.90302624304581514, -3037.47987111324800935 -609.02601344185222842, -2993.82709496418010531 -628.0016712460569579, -2972.00070688964569854 -608.36988085943266924, -2922.53465376360782102 -658.23550415873842212, -2823.60254751153024699 -639.8334361576091851, -2777.11234093232906162 -613.03133802493107396, -2684.13192777392850985 -665.09347402553498796, -2628.03275474647944066 -686.31816140657201686, -2599.98316823275399656 -669.71750447631166026, -2566.28919555170341482 -671.20429687245177774, -2549.44220921117903345 -640.70212277882797025, -2515.28934145543917111 -717.7851105966610703, -2481.13647369969930878 -714.98828100707555677, -2446.98360594395944645 -679.12116700962542382, -2416.14189245485340507 -673.34055495922484624, -2385.30017896574736369 -690.69965338020710988, -2354.45846547664132231 -638.45287846768269446, -2328.09517633439554629 -668.74469845741441532, -2301.73188719214977027 -632.03047506117445664, -2275.36859804990399425 -683.83382993271811756, -2179.26749590189592709 -652.66902542340085347, -2131.68382859142275265 -683.46074223017581062, -2084.10016128094775922 -735.91181029677386505, -2036.51649397047458478 -692.11033700469715768, -1933.45313963446915295 -650.80562701733924769, -1830.30583781972472934 -707.76372913913564844, -1702.79938199450316461 -718.06932595534181019, -1662.82398039400959533 -747.4441975176869164, -1642.8362795937619012 -722.72361913185363846, -1548.05589767017681879 -639.62458159588413764, -1520.83321568552401004 -682.76498331747984594, -1466.38785171621657355 -632.481410050083241, -1418.65952462968107284 -678.03477329064230616, -1370.93119754314739112 -660.02244924548767813, -1323.2028704566118904 -673.96818015412759451, -1293.46875438188271801 -665.97971985197955291, -1263.7346383071553646 -720.34986500859213265, -1234.0005222324261922 -714.82634976335884858, -1189.87199123714799498 -659.86998241715355107, -1101.61492924658978154 -657.17553222927426759, -1073.07939400062878121 -682.36355899866453001, -1016.00832350870859955 -686.27564796459137142, -937.94145886259957479 -660.23573885769133085, -861.48603904372885154 -674.12628997348406301, -780.15951413025959482 -641.47594102666721483, -715.1263175664598748 -648.32833612746776453, -682.60971928456001478 -629.73630989402136038, -583.87739251328002865 -623.78335404144490894, -534.51122912765004003 -592.82699196944145115, -455.97124939492914564 -615.35429008460573641, -408.15374758111920528 -639.92217449407280583, -360.33624576730926492 -597.42377650831781466, -312.51874395349932456 -609.84935497193305309, -284.24938990047030529 -629.30205174019147307, -227.71068179441954271 -622.47708237273559462, -150.18158376638984919 -631.10817174098951909, -125.84453268690867844 -664.93210970406926208, -77.17043052795906988 -643.63442368162668572, 72.20252947487006168 -672.91418681670643309, 133.86666948555011913 -653.19640086365416209, 176.97527199587148061 -675.26601429714037295, 198.52957325103034236 -685.86143712075750045, 235.7989664453698424 -674.28967414381531853, 310.33775283403974754 -670.86656372890092825, 373.34901391307994345 -690.20615382406344906, 485.66354329149999103 -612.70366926919587058, 580.68034040603106405 -632.42739168687285201, 672.07872737845082156 -625.77153012181656777, 740.9693480522300888 -631.05312416772039796, 775.41465838912063191 -642.90702796954769838, 823.55699965800977225 -603.35180270367459343, 871.69934092690073157 -604.22682737090440241, 919.84168219578987191 -626.27586063797662064, 977.72580402940093336 -584.14130729667431297, 1026.26881099233014538 -599.43215571673977138, 1123.35482491817037953 -643.78485246596574143, 1154.4662194237798758 -666.49700075838154589, 1185.577613929400286 -626.14014775339774133, 1216.68900843500978226 -652.31891067151605057, 1279.74764411979140277 -624.94189165515194873, 1311.27696196218039404 -637.44580474748295273, 1328.89335091626981011 -601.81945130120357135, 1346.50973987036104518 -626.22691665321644905, 1364.12612882445046125 -641.58509579898668562, 1462.69308716767136502 -650.76387091452647837, 1555.10993490623059188 -683.67214228356283456, 1601.3183587755111148 -641.19042522728977929, 1721.63802144146120554 -677.96215989525580881, 1751.7224171317911896 -735.03355516963029004, 1781.80681282212117367 -741.38823747205469772, 1811.89120851245115773 -673.82201947085650318, 1855.39854866148107249 -719.03922996383789723, 1942.41322895952089311 -692.55438028385060534, 1990.71657389797019277 -679.91578208264104433, 2014.86824636719120463 -679.43318562920399017, 2109.32948062179002591 -716.5136358755009951, 2203.72379823444043723 -726.73104148764787169, 2236.63991727033044299 -762.15965436323836002, 2302.47215534212136845 -705.75646305411100911, 2330.36113100389138708 -743.45267124305087236, 2358.25010666566140571 -711.33816593357300917, 2386.13908232743142435 -701.63355035235622381, 2409.59777000343001419 -695.0412146831249629, 2456.51514535543083184 -702.54482331856479504, 2547.09546839912127325 -728.88080257596811862, 2592.38562992096103699 -747.06340432397269069, 2617.640709350301222 -752.48989321253066009, 2668.15086820895976416 -734.04723043037347452, 2726.39367460033008683 -752.98920646052579286, 2755.51507779601070069 -741.50230287846034116, 2831.00179011404088669 -694.35638567771911767, 2866.29483080771115056 -715.23084019532029743, 2936.88091219506986818 -721.21498138357014795, 3008.43858555339011218 -726.47287416731819576, 3053.79054033515149058 -752.38397527608162818, 3076.46651772603127029 -740.82715736131717676, 3178.83706671986055881 -707.07239739419765101, 3255.99361642457097332 -731.89172238988203389, 3294.57189127693072805 -751.97815533444395442, 3333.6187171074006983 -730.12915453660775711, 3411.71236876836064766 -714.20953798166738125, 3428.97469610231109982 -714.27139950878358832, 3463.4993507702010902 -693.79121922104286568, 3508.20573273827994853 -688.94297428684194529, 3552.91211470636062586 -703.41349749440973937, 3597.61849667444130318 -667.42835204757716383, 3655.91878296326012787 -731.35282986201696076, 3685.06892610768136365 -705.83079911225627256, 3719.63721673821146396 -753.91922519133186142, 3736.92136205347105715 -711.26763920485336712, 3764.91603789243981737 -750.44245503906245176, 3792.91071373142131051 -764.42503775494674301, 3820.90538957039007073 -715.37047605126667804, 3961.08824116563027928 -738.40795611779708452, 4003.70269562589146517 -747.31750841432926791, 4046.31715008615992701 -696.82305481066691755, 4088.93160454643020785 -744.08635086677554682, 4135.43322152124983404 -724.7108157826723982, 4181.93483849608037417 -728.72841414861522935, 4228.4364554709109143 -725.93724856186645411, 4274.50684137697044207 -764.15301538522157898, 4366.6476131890913166 -760.89610974437323421, 4387.44986995130147989 -746.93810323822663122, 4429.05438347573090141 -747.14676812790776239, 4469.70192952305023937 -724.93407713495798816, 4550.99702161769073427 -728.2890022678952846, 4594.22217304462992615 -724.89843764512716007, 4637.44732447156002308 -701.98910163413006558, 4680.67247589850103395 -729.86743523787708909, 4721.13517775475975213 -703.70156171690155134, 4802.06058146728992142 -719.58542068370638844, 4836.81655575535023672 -721.62355666390158149, 4854.19454289937038993 -688.94986673148378031, 4885.42602291939056158 -684.29873376897876369, 4916.65750293941982818 -695.69131084083983296, 4947.88898295943999983 -716.76671885326186384, 4970.12775986229007685 -712.77431978867002726, 4992.36653676515106781 -711.87176926608071881, 5014.60531366801023978 -718.46365048487905369, 5062.75577723057085677 -646.82839001369984544, 5159.0567043557011857 -713.27495319382364869, 5237.30667745837945404 -695.11518350527717303, 5276.43166400972131669 -690.65227479415716516, 5295.75120249165138375 -727.87009848414140833, 5315.07074097359236475 -697.84581478174050062, 5334.39027945552970777 -701.86460185122155053, 5437.0297344663495096 -717.25015723107253507, 5473.58887736257111101 -719.83918301829112352, 5491.86844881068191171 -686.20699917946080859, 5554.16494060359127616 -708.04999256934161167, 5585.31318650005141535 -717.70621047862891828, 5660.01842714526083 -694.16125823509764814, 5686.98473318712149194 -704.74038383889842407, 5740.91734527083917783 -670.96149344006789761, 5814.49066733738891344 -649.41706474840748342, 5857.18002753217024292 -707.6650804031721691, 5899.86938772694065847 -713.13295682599959946, 5942.55874792172198795 -695.0498670605074949, 6007.75818295154113002 -624.15052079908423366, 6046.70854686456095806 -682.43280400287153498, 6124.60927469061152806 -609.16431744624765088, 6216.9279195611097748 -659.99326950804834269, 6263.08724199636071717 -630.89395080667941329, 6326.24796405009055889 -595.10322571677238557, 6397.20513770685010968 -637.60681662853380658, 6432.68372453522988508 -647.49135148171262699, 6486.51765440133112861 -629.30745056620071409, 6513.43461933438175038 -616.36485099298306523, 6631.86393353866969846 -643.594426945355508, 6737.27373795032053749 -658.26993608687394044, 6764.89023265933883522 -645.84500259983315118, 6792.50672736836077092 -616.51203817084729053, 6820.12322207737906865 -636.16267307207795056, 6890.61998227112144377 -662.97879186425734588, 6925.86836236797989841 -648.58048445890199218, 6982.99969691730166232 -586.82141765668234257, 7066.36203947452031571 -564.95358928862060566, 7100.56024754044938163 -627.01166655370298031, 7117.65935157342119055 -589.10097139369372599, 7158.45720425399213127 -553.17956217464370638, 7240.05290961513037473 -579.09965342174609759, 7261.12488385148117231 -544.32144923624991861, 7282.19685808783924585 -542.40078862543168725, 7303.26883232419004344 -527.66724123582139327, 7329.35415312834174983 -529.50723370113291821, 7355.43947393250073219 -512.30876716394959658, 7381.52479473665971454 -510.92086990549250913, 7423.50982351500078948 -507.38195090882391014, 7465.49485229334186442 -518.85261949053051467, 7507.47988107167930139 -495.47263879747470128, 7603.05656535038087895 -479.8333480460089504, 7650.84490748972984875 -466.57776693697587689, 7690.57123266231155867 -455.32303235237600347, 7730.29755783488963061 -462.49399795460431051, 7770.0238830074604266 -475.0856950523566411, 7874.53231576474081521 -462.6912207326117823, 7911.56850013669190957 -428.73851463087908087, 7948.60468450865027989 -451.27197642470491701, 7985.64086888061228819 -469.69507989201952114, 8042.13128037644946744 -428.99767385111181284, 8070.37648612435896212 -433.53360038361506668, 8169.31938505191010336 -442.27266329189319549, 8218.79083451569022145 -498.49448286928577545, 8283.02253039451898076 -485.50585029640160428, 8315.13837833394063637 -433.20464027491902925, 8339.52442067441006657 -485.69275673028755591, 8388.29650535534892697 -468.32217975811954602, 8500.90227764899100293 -478.77221435616047529, 8521.47039153274090495 -424.33569645220450184, 8542.03850541649808292 -474.07085166306433166, 8562.60661930025889887 -487.16451705157373908, 8590.6373765013886441 -518.88687026264778979, 8618.66813370251838933 -465.42787408579056319, 8646.69889090365904849 -477.05058796106959562, 8691.8003157485909469 -487.17866413375350021, 8714.35102817105871509 -466.7564660110767818, 8822.26291358752860106 -458.24088943273545738, 8868.40885741727834102 -504.30054950419844317, 8960.70074507678145892 -503.84828440035698804, 8980.39798267609148752 -455.98211704716686654, 9019.79245787470790674 -483.76520147900009761, 9074.4967084180607344 -461.57007838582012482, 9137.6866437639000651 -466.22476882580690472, 9169.28161143681791145 -492.08044608349678128, 9255.9715483275904262 -499.04001331140898401, 9299.31651677297850256 -485.81168072872287667, 9420.96278016371070407 -511.34325688668900511, 9450.90389236509145121 -529.91344311772263609, 9480.84500456646856037 -518.9444550704017729, 9510.78611676783839357 -515.62987959694305573, 9610.94816651913060923 -560.67809543371504333, 9680.32558046235863003 -576.24640701603470916, 9812.26057487028083415 -600.70758190904348339, 9754.20013022578859818 -671.37802562230649528, 9645.63687349074098165 -670.78273566125835714, 9610.94816651913060923 -725.83081235238068984, 9577.56081660202835337 -674.07587381566145268, 9544.17346668494064943 -718.94195208652058682, 9510.78611676783839357 -708.49116147091422135, 9420.96278016371070407 -650.13572207200354569, 9380.41402570013815421 -675.97984736615967449, 9339.86527123655832838 -635.18746945690782013, 9299.31651677297850256 -673.57857486088937549, 9212.62657988220962579 -642.63143344754666941, 9169.28161143681791145 -642.28931371432258857, 9106.09167609097858076 -654.06777672708722093, 9074.4967084180607344 -647.84257149780160034, 9056.26195823694069986 -610.43810671338883367, 9038.02720805582794128 -596.0603953192978679, 9019.79245787470790674 -645.59352926042106446, 9000.09522027539787814 -614.7539492635996794, 8960.70074507678145892 -608.2503081790887336, 8914.55480124702808098 -631.212952063557168, 8822.26291358752860106 -661.81789526566649329, 8786.29228511537075974 -657.15652048282709075, 8750.32165664322019438 -623.82966697192887295, 8714.35102817105871509 -661.08966113534961551, 8669.24960332611954072 -612.44283674073494694, 8646.69889090365904849 -611.17654320961651138, 8562.60661930025889887 -616.81246751840603793, 8500.90227764899100293 -648.83922708476779917, 8463.36702021777091431 -598.39683280995132009, 8425.83176278655810165 -656.65988938066766423, 8388.29650535534892697 -623.67234518178065628, 8363.91046301487949677 -589.91672465183773966, 8315.13837833394063637 -592.82861785949398836, 8250.90668245510096313 -622.16675962622525731, 8218.79083451569022145 -618.26323693428639672, 8119.8479355881399897 -582.04127193360636738, 8070.37648612435896212 -573.75624777593611725, 8013.88607462852178287 -585.74660439962553937, 7985.64086888061228819 -582.37432917740306948, 7874.53231576474081521 -616.68118156722107415, 7839.69617151231159369 -566.52903207206986735, 7804.86002725988964812 -597.99963760223522513, 7770.0238830074604266 -588.12239852682114361, 7650.84490748972984875 -596.69756863122347568, 7555.26822321103190916 -606.78430134736800028, 7507.47988107167930139 -672.97844356164682722, 7381.52479473665971454 -682.30309052713528217, 7303.26883232419004344 -712.03877138982375072, 7240.05290961513037473 -744.71454958676667957, 7199.25505693455943401 -689.79410747640031332, 7117.65935157342119055 -755.93711474216479473, 7083.46114350748121069 -752.19989855869198436, 7066.36203947452031571 -721.79939821591278815, 7038.57459195544015529 -763.51731997249453343, 7010.78714443637090881 -776.37641110780555209, 6982.99969691730166232 -794.42393854600913983, 6963.95591873419925832 -730.30873293712329541, 6944.91214055108957837 -783.88947785305344951, 6925.86836236797989841 -791.55938686081140077, 6855.3716021742520752 -772.26611310734801918, 6820.12322207737906865 -769.96434496835763639, 6737.27373795032053749 -755.39308719340669995, 6702.13713647977147048 -752.21752371000502535, 6667.00053500922240346 -777.10386377352392628, 6631.86393353866969846 -803.86330854391258072, 6592.38749547057977907 -794.43083013174873486, 6552.91105740247166977 -769.65422106346386499, 6513.43461933438175038 -754.7268984782501775, 6459.60068946828050684 -789.29971970510882784, 6432.68372453522988508 -820.37619984408820528, 6361.72655087847033428 -767.93633310210952914, 6326.24796405009055889 -761.09577624489725167, 6305.19439003217939899 -758.98963704041352685, 6284.14081601427187707 -759.60898691502870861, 6263.08724199636071717 -785.96678399577695018, 6170.76859712585883244 -772.81309670767632269, 6124.60927469061152806 -755.00838912191488816, 6085.65891077759170003 -799.80950901622054516, 6007.75818295154113002 -824.9768398381629595, 5986.02503794160020334 -784.34726626249857873, 5964.29189293165927666 -793.25083498492040235, 5942.55874792172198795 -819.45298642603961525, 5814.49066733738891344 -857.55471557325608956, 5789.96622664854021423 -832.08319834826647821, 5765.44178595969151502 -829.41811417773533321, 5740.91734527083917783 -853.49500236674407461, 5713.95103922898215387 -863.32914494868282418, 5660.01842714526083 -860.63820039368852122, 5635.11668026353163441 -848.30770133077817263, 5610.21493338179152488 -815.64434926484500465, 5585.31318650005141535 -852.8963108215621105, 5523.01669470713113697 -881.63667741981862491, 5491.86844881068191171 -841.13649747865838435, 5455.30930591446031031 -830.20342006338046303, 5437.0297344663495096 -850.84054749445408561, 5402.81658279607017903 -834.58726531838965457, 5368.60343112580176239 -818.94320779260965537, 5334.39027945552970777 -862.60437808995129672, 5276.43166400972131669 -840.0323078055116639, 5198.18169090704122937 -820.06388566214650382, 5159.0567043557011857 -820.45782097735991556, 5110.90624079313147377 -796.73985369011279545, 5014.60531366801023978 -860.21764409460411116, 4947.88898295943999983 -870.88930186007632983, 4854.19454289937038993 -819.06468368074183672, 4819.43856861132098857 -811.78214785120189845, 4802.06058146728992142 -860.60938496826383926, 4761.59787961103120324 -821.93035650179399454, 4680.67247589850103395 -896.56626783266779057, 4550.99702161769073427 -893.24964416304214865, 4510.34947557037139632 -929.70069133159449848, 4429.05438347573090141 -891.81893183557531302, 4408.25212671350982419 -911.29485244005718414, 4366.6476131890913166 -950.93941600364837541, 4320.57722728302996984 -894.46917999626521123, 4228.4364554709109143 -855.23726371382304023, 4088.93160454643020785 -871.84301741071749348, 3961.08824116563027928 -875.96957104592615906, 3914.36062396721990808 -894.36424004273158062, 3867.63300676880044193 -864.91732916426235533, 3820.90538957039007073 -880.86201781130284871, 3736.92136205347105715 -909.83473802531943875, 3702.35307142294095684 -887.87877353687190407, 3685.06892610768136365 -874.27015102595555618, 3626.76863981884980603 -868.20104299040031037, 3597.61849667444130318 -873.67044824728736785, 3463.4993507702010902 -838.41263497590261977, 3446.23702343625063804 -882.82367922537787308, 3411.71236876836064766 -844.3277500074332238, 3372.66554293787976349 -846.46536789812216739, 3294.57189127693072805 -876.90167607784269421, 3217.41534157222031354 -879.85923443342335304, 3178.83706671986055881 -887.62315618699130937, 3144.7135503885901926 -880.79333016300051895, 3110.59003405731073144 -839.90974336732438132, 3076.46651772603127029 -879.2235882596069132, 3031.11456294426989189 -869.55782806217007419, 3008.43858555339011218 -937.68884923943119247, 2984.58602776729003381 -851.89778810387974772, 2960.73346998118086049 -865.26477722960635219, 2936.88091219506986818 -882.02332125860289125, 2901.58787150139050937 -830.22587082508721323, 2831.00179011404088669 -896.63832563621394911, 2805.83955267469082173 -857.49944022137515276, 2780.67731523534985172 -845.11515534314025899, 2755.51507779601070069 -874.46054115409629048, 2697.27227140464037802 -936.16605825026294951, 2668.15086820895976416 -912.93374074457960887, 2642.89578877963049308 -898.58418416176755272, 2592.38562992096103699 -862.2957105891507581, 2501.80530687727969053 -856.62995125284373898, 2456.51514535543083184 -852.63213739615571285, 2433.05645767943042301 -834.57756392525607225, 2386.13908232743142435 -865.52891985455426038, 2302.47215534212136845 -848.03384814538208047, 2269.55603630623136269 -875.29452712116062685, 2203.72379823444043723 -874.11600209693324359, 2172.25902569688969379 -895.35642047925171028, 2140.79425315934076934 -877.18706670652181856, 2109.32948062179002591 -863.89224685466979281, 2077.84240253693042177 -863.29358058108959995, 2046.35532445205990371 -796.86074882455636725, 2014.86824636719120463 -832.8202835587426307, 1966.56490142874008598 -839.8558702065217858, 1942.41322895952089311 -836.49394297417711641, 1898.9058888105000733 -813.14296412110115853, 1811.89120851245115773 -911.8144687130411512, 1721.63802144146120554 -831.62534884552314907, 1681.53146721948087361 -854.93437695663669729, 1641.42491299749144673 -853.98002716670634982, 1601.3183587755111148 -831.33617299280376756, 1508.90151103695006896 -815.7542821424531212, 1462.69308716767136502 -790.54225545883173254, 1429.83743438658984815 -774.42628563408698028, 1396.98178160552106419 -807.08024899902261495, 1364.12612882445046125 -756.46060859036333568, 1311.27696196218039404 -827.77283332508159219, 1248.21832627740059252 -787.22715704050142449, 1216.68900843500978226 -795.75538903271080926, 1123.35482491817037953 -733.32374426968340231, 1074.81181795525026246 -729.88818725302780877, 977.72580402940093336 -757.04401286552138117, 958.43109675153118587 -784.20450836323061594, 939.13638947366143839 -754.1782818901842802, 919.84168219578987191 -773.26807762795397139, 775.41465838912063191 -777.87818788049821705, 706.52403771534136467 -752.08552894817603374, 672.07872737845082156 -817.93027086618417343, 641.61259838763999142 -822.03905872636187269, 611.14646939684007521 -815.87999075781817737, 580.68034040603106405 -837.59384648987111177, 549.00807470118070341 -774.93629869722508374, 517.33580899634125672 -759.64054713955829357, 485.66354329149999103 -808.91852177362579823, 448.22536683203088614 -824.95908928184871911, 410.78719037255086732 -803.49373760593516636, 373.34901391307994345 -787.36057313562628224, 352.34526022007139545 -797.47992607057835812, 331.34150652705011453 -793.02309540194642068, 310.33775283403974754 -825.24016527194976334, 273.06835963971116144 -819.79976627150745117, 198.52957325103034236 -800.57420125386943255, 155.42097074071079987 -814.71829661613060125, 133.86666948555011913 -836.51555774687085432, 113.31195614866101096 -842.58590117868538982, 92.75724281177008379 -811.56060690080812492, 72.20252947487006168 -800.22454720237942638, 22.41154280726095749 -825.54462806917422313, -27.37944386034996569 -804.38177145106806165, -77.17043052795906988 -788.33228858176335052, -101.50748160744024062 -833.12361483519248395, -150.18158376638984919 -809.45877047022349871, -176.02461644239974703 -754.02035147157880601, -201.86764911840964487 -735.36152694490351678, -227.71068179441954271 -752.71698962144023426, -255.98003584744856198 -784.148045454996236, -312.51874395349932456 -761.63875050319666116, -455.97124939492914564 -753.96841765755607412, -482.1512426391700501 -774.4983414422927126, -508.33123588340913557 -764.08164659068711444, -534.51122912765004003 -794.79385552424946582, -633.24355589891911222 -735.12471670483137132, -682.60971928456001478 -762.82621543062850833, -747.64291584835973481 -748.5029136270154595, -780.15951413025959482 -753.73821158015903166, -807.26835576808025507 -807.74691761956364644, -834.37719740591001027 -812.02352712590641204, -861.48603904372885154 -839.00534892164864686, -886.97117898335000064 -826.47058608914267097, -912.45631892298024468 -802.54261133304248688, -937.94145886259957479 -792.65039589870798409, -963.96374707796985604 -794.40372605750508228, -989.98603529334013729 -836.79545861448764299, -1016.00832350870859955 -865.82409551505497802, -1044.54385875466959988 -814.3846817473468036, -1101.61492924658978154 -799.42697343223630924, -1145.74346024186979776 -789.85190271033548015, -1234.0005222324261922 -839.86504015712171167, -1323.2028704566118904 -846.8079866452656006, -1466.38785171621657355 -835.15430429941557122, -1493.6105337008693823 -795.81927985987454122, -1548.05589767017681879 -798.22428409041140185, -1579.64935831137245259 -838.13608999741359185, -1611.2428189525662674 -846.85763619234262478, -1642.8362795937619012 -826.58250718293902537, -1682.81168119425547047 -833.74983353622678806, -1702.79938199450316461 -876.33633022205958696, -1745.30153393624368618 -826.27792698366056356, -1787.80368587798420776 -797.1025051982903733, -1830.30583781972472934 -838.58617125719410978, -1864.68827175797287055 -826.21056586856252579, -1899.07070569622101175 -836.52255384068757849, -1933.45313963446915295 -850.01801350227833609, -1967.8075910798042969 -833.71440553436946175, -2002.16204252513944084 -830.81187174063484235, -2036.51649397047458478 -817.78088455600209272, -2179.26749590189592709 -872.38440224597979977, -2211.30119661789922247 -848.85747215254468756, -2243.33489733390069887 -813.50091989275915694, -2275.36859804990399425 -792.20941844024241618, -2354.45846547664132231 -840.90607208804954098, -2446.98360594395944645 -848.55902192855364774, -2549.44220921117903345 -857.64248511564596811, -2583.13618189222961519 -799.03348171629772878, -2599.98316823275399656 -822.32587122863765217, -2656.08234126020306576 -804.44624664219372789, -2684.13192777392850985 -803.48495572170281775, -2730.62213435312969523 -762.09338727268891489, -2823.60254751153024699 -802.90859322101869111, -2873.06860063756812451 -791.14607628716748877, -2972.00070688964569854 -753.51284861314206864, -3015.65348303871360258 -798.17575279821835466, -3037.47987111324800935 -740.96097600945722661, -3132.18241611493522214 -782.54834266276930066, -3179.53368861577928328 -795.7395667738442171, -3269.70601499599979434 -846.23045628376621607, -3307.96390165746197454 -851.50507584640172354, -3327.09284498819306464 -808.17968114133987001, -3434.99928368946348201 -818.0250131964207867, -3452.4688072902345084 -816.69514791008100474, -3469.93833089100644429 -785.59631151303415209, -3487.40785449177747068 -859.29944403827312271, -3513.80535691308796231 -811.91193862997556607, -3566.60036175571076456 -845.59070835820375578, -3600.1266797075732029 -818.88218119318707977, -3667.1793156112989891 -876.81600023682153733, -3739.87713456037727155 -869.36642378948340593, -3802.20678629147278116 -857.56125940234642258, -3833.37161215702053596 -865.98475170386268474, -3871.49509185795159283 -847.56198760658799074, -3909.61857155888355919 -834.17140100623396393, -3947.74205125981461606 -888.38262042994938383, -4029.09385256345285597 -840.9261606644170115, -4069.76975321527243068 -876.66127671486583495, -4211.43887508883653936 -873.00634054451688826, -4245.48442473378872819 -907.86230308306289771, -4313.57552402369401534 -849.63544022605810824, -4367.11017807210009778 -854.26458677793084462, -4497.61452091723913327 -857.85934619817362545, -4548.92843065448323614 -824.1524382880545545, -4570.89054269839834888 -849.28283820317483332, -4592.85265474231255212 -844.8124876908314036, -4614.81476678622766485 -809.39616228278487142, -4657.93842697693435184 -840.36930009782508932, -4679.50025707228724059 -796.0073582812665336, -4706.4330129202662647 -770.2350731861326949, -4760.29852461622431292 -763.37997239749529399, -4790.60447655938605749 -765.38236742231265453, -4820.91042850254871155 -786.28666164494734403, -4851.21638044571045612 -812.61955108995607588, -4909.90218491490577435 -809.9224652956090722, -4939.24508714950297872 -782.50256072929300899, -5017.37359183851367561 -833.96109019694131348, -5056.43784418301856931 -773.99704415542305469, -5097.70397744204547053 -794.72438152579707094, -5138.97011070107237174 -794.53135550277920629, -5180.23624396009927295 -781.27855710917037868, -5222.72063707872712257 -775.98634975122445212, -5265.20503019735497219 -760.81180127274501501, -5307.6894233159837313 -800.21357747476326949, -5354.93001374309642415 -779.68617483489356346, -5449.41119459732180985 -816.43476793739000641, -5536.98067856846682844 -797.12236939367676314, -5556.71791187837698089 -814.55184835892305273, -5596.19237849820183328 -771.34418488440041983, -5674.91272565030885744 -800.5057297577193367, -5726.82654223158442619 -791.97564040046677292, -5752.78345052222266531 -780.168067863250144, -5813.72231077188371273 -802.71189805850849552, -5842.0224270186636204 -844.44957598587961911, -5870.32254326544352807 -804.65649620518342999, -5898.62265951222343574 -824.54107759303724379, -5945.47240115755903389 -795.91525509729376608, -6039.17188444823113969 -824.19345657886310619, -6069.21481591180508985 -756.79906772274102877, -6129.3006788389520807 -813.46172833235391408, -6148.45959323880470038 -782.02877053831412013, -6186.77742203851084923 -785.93381224034078514, -6243.31958909722197859 -811.11473361583375663, -6271.59067262657936226 -802.60848015690885404, -6414.47243664319648815 -814.79629754459961077, -6454.49925772666483681 -822.33932511288048772, -6494.52607881013136648 -811.4749625823687893, -6534.55289989359880565 -788.08811041551984999, -6583.28711997248865373 -801.45354001107352815, -6632.02134005137759232 -791.96974826285122617, -6680.7555601302674404 -770.61659152655465732, -6778.80545180718399934 -779.1009932864953953, -6804.13786870596322842 -805.98100434246271107, -6854.80270250352168659 -791.93474664174573263, -6872.96710842110041995 -821.0313142171266918, -6891.13151433868006279 -792.40189850355795897, -6909.29592025625879614 -789.16330499729292569, -6984.6201504748833031 -779.36976502405877909, -7022.28226558419555658 -779.92701152741869919, -7061.67066531439104438 -752.51641880731244783, -7101.05906504458653217 -791.03773660261776968, -7140.44746477478201996 -778.50823280253166558, -7274.11188143560775643 -801.58874432453831105, -7317.34165279746503074 -813.75633682829675308, -7403.80119552117776038 -863.68429638150269056, -7432.38180304209799942 -868.55919436974681958, -7460.96241056301641947 -860.14260465537290656, -7489.54301808393483952 -861.37034735947781883, -7540.43330369200975838 -825.03905127541452202, -7565.87844649604630831 -825.49843084486042244, -7659.09495649730797595 -882.08990176227689517, -7746.91009119145292061 -783.50522166691621351, -7790.81765853852630244 -858.49530993877078799, -7915.95233600324809231 -851.56527253852050308, -7941.65700876117625739 -808.18737076301931666, -7967.36168151910442248 -812.53964645688438395, -7993.06635427703258756 -821.4924145995219078, -8023.16901064906323882 -779.83749175818593358, -8053.27166702109298058 -798.58570498797871551, -8083.37432339312454133 -802.93879759002516039, -8222.9203252389197587 -770.51532552057233261, -8278.54850630083819851 -779.20060960742125644, -8347.82589665416526259 -769.84911090499372222, -8382.46459183082697564 -698.0631283975169481, -8408.40554450025956612 -723.0170404843020151, -8460.28744983911747113 -686.72014631536262641, -8608.24671795633184956 -725.70406983194106942, -8652.63677605182965635 -701.9543651080705331, -8741.41689224282890791 -696.37532631321096233, -8832.4608387892585597 -759.66912549264475274, -8873.45367449881086941 -745.16436306908826737, -8955.43934591790821287 -688.36773069604828379, -9003.73442267820064444 -729.92627108677697834, -9052.02949943848943803 -750.2127323837808035, -9100.32457619878186961 -743.6641059126836808, -9154.68065642196597764 -763.55731252340797255, -9192.30955047796851431 -710.00693958335295974, -9267.56733858997540665 -741.55512657213444072, -9312.16078509670478525 -694.25755986236094941, -9401.34767811016172345 -734.38367638440445262, -9450.09114724816572561 -743.60463469704541239, -9498.83461638617154676 -678.54521333459092602, -9547.57808552417554893 -697.63283341287569783, -9593.79009023376056575 -698.16438856745048724, -9640.00209494334922056 -744.36103688960474756, -9686.21409965293423738 -758.12686495986258706, -9728.16592205132837989 -752.876902634200178, -9770.11774444971888443 -734.8619786790766284, -9812.06956684810938896 -731.35202656783280872, -9942.05015998918315745 -755.60272053193966713, -9962.12133353558419913 -740.49702058811499228, -10002.26368062838810147 -680.87017332395726044, -10038.16048616017360473 -674.07796318271016389, -10109.95409722374097328 -693.81394153774272127, -10168.89864711592053936 -676.94008410800870479, -10198.3709220620112319 -768.09905717864421604, -10225.53112954944663215 -720.65414349171328467, -10252.69133703688567039 -744.01119510814305613, -10279.85154452432107064 -706.242155959692127, -10351.26629470117950405 -727.20130718660084312, -10370.71422849830196355 -699.92159131887888179, -10409.61009609254688257 -731.22095539887550331, -10466.08085725326600368 -725.14590830307452052, -10494.31623783362374525 -758.89955742179836307, -10584.76880504294240382 -751.18304283765564833, -10634.09925949202079209 -731.6135347515603371, -10683.42971394110281835 -711.20935614022141635, -10732.76016839018120663 -768.324178074901738, -10797.10059908131006523 -763.16992584450895265, -10829.27081442687267554 -791.04828790775036396, -10873.18295137666427763 -782.23774949246649157, -10961.00722527624748182 -819.47527544352055884, -11100.81483194136308157 -775.06119302690603945, -11182.35379109605128178 -791.79639142738733426, -11163.62430071464405046 -630.21399003800638638))'

    np_wkt = change_coords_precision(p_wkt, precision0)
    nq_wkt = change_coords_precision(q_wkt, precision0)

    print(np_wkt)
    print(nq_wkt)

    POLYGON ((-11638 1091, -11591 1166, -11574 1178, -11557 1101, -11510 1083, -11463 971, -11417 1073, -11373 1096, -11285 1021, -11221 1013, -11189 1179, -11041 1187, -11010 1061, -10980 1043, -10950 1078, -10894 1190, -10865 1112, -10846 1207, -10807 1210, -10783 1137, -10759 1135, -10736 1210, -10654 1057, -10595 1080, -10566 1181, -10530 1241, -10458 1174, -10438 1217, -10398 1109, -10354 1201, -10311 1068, -10268 1204, -10142 1066, -10003 1056, -9857 1181, -9813 1109, -9723 1157, -9686 1120, -9610 1085, -9592 1059, -9574 1142, -9556 1188, -9411 1106, -9370 1192, -9288 1235, -9258 1171, -9228 1128, -9197 1095, -9153 1220, -9064 1167, -9015 1056, -8965 1063, -8916 1155, -8890 1154, -8838 1161, -8769 1123, -8734 1099, -8716 1165, -8697 1189, -8679 1152, -8632 1126, -8586 1078, -8539 980, -8449 993, -8372 993, -8330 944, -8288 1074, -8247 1098, -8159 957, -8115 961, -8084 1015, -8053 1101, -8022 1094, -7971 1049, -7945 1082, -7860 1035, -7816 1061, -7730 1074, -7685 1052, -7641 965, -7596 1050, -7478 1006, -7403 1022, -7365 966, -7311 994, -7285 1102, -7235 973, -7202 965, -7169 961, -7137 1142, -6990 1099, -6870 1069, -6823 1151, -6775 1126, -6727 1174, -6671 1026, -6643 1076, -6623 1002, -6585 1113, -6555 1099, -6495 1157, -6448 1133, -6354 1036, -6269 977, -6249 951, -6229 1085, -6209 961, -6157 961, -6131 1166, -6104 1120, -6078 981, -6052 1096, -6032 1003, -5993 989, -5964 1008, -5934 1049, -5905 1179, -5858 1042, -5763 1176, -5636 989, -5512 960, -5434 984, -5395 1036, -5336 992, -5307 1089, -5216 1140, -5189 1091, -5135 1135, -5092 992, -5071 942, -5005 1087, -4988 903, -4970 926, -4953 1060, -4910 1028, -4866 889, -4823 921, -4805 932, -4787 889, -4769 1037, -4735 919, -4667 898, -4620 951, -4573 1076, -4526 1019, -4444 902, -4404 900, -4289 939, -4227 1055, -4196 939, -4171 1050, -4147 1018, -4123 1053, -4089 993, -4022 1080, -3996 1085, -3943 1019, -3891 972, -3855 1031, -3819 1066, -3783 1072, -3745 948, -3725 1042, -3695 993, -3665 1118, -3635 1175, -3541 1017, -3493 1109, -3450 1054, -3428 1088, -3378 1019, -3279 1060, -3233 1151, -3140 1009, -3084 966, -3056 1047, -3022 1038, -3005 1118, -2971 959, -2937 970, -2903 1086, -2872 1067, -2841 1015, -2810 1090, -2784 1016, -2758 1129, -2731 1003, -2635 1128, -2587 1103, -2540 912, -2492 1027, -2389 1107, -2286 975, -2159 944, -2119 906, -2099 929, -2004 1110, -1977 1002, -1922 1115, -1874 1063, -1827 1095, -1779 1064, -1749 1082, -1720 959, -1690 949, -1646 1069, -1557 1112, -1529 1035, -1472 1006, -1394 1107, -1317 986, -1236 1057, -1171 1027, -1138 1064, -1040 1093, -990 1150, -912 1136, -864 1043, -816 1155, -768 1127, -740 1145, -683 1117, -606 1061, -582 1031, -533 1098, -384 1041, -322 1097, -279 1045, -257 971, -220 1043, -145 1033, -82 956, 30 1167, 125 1136, 216 1112, 285 1079, 320 1023, 368 1100, 416 1138, 464 1062, 522 1186, 570 1139, 668 1017, 699 992, 730 1104, 761 1026, 824 1141, 856 1080, 873 1146, 891 1110, 908 1038, 1007 1101, 1099 1014, 1146 1110, 1266 1061, 1296 943, 1326 915, 1356 1072, 1400 938, 1487 977, 1535 1030, 1559 1077, 1654 945, 1748 951, 1781 914, 1847 1001, 1875 947, 1902 1029, 1930 1000, 1954 1039, 2001 1037, 2091 990, 2137 939, 2162 960, 2212 1011, 2271 949, 2300 987, 2375 1052, 2411 1019, 2481 1017, 2553 1010, 2598 961, 2621 954, 2723 1046, 2800 1021, 2839 920, 2878 978, 2956 982, 2973 996, 3008 1012, 3052 1070, 3097 987, 3142 1081, 3200 951, 3229 1045, 3264 911, 3281 1051, 3309 985, 3337 949, 3365 1022, 3505 949, 3548 907, 3591 1046, 3633 943, 3680 977, 3726 998, 3773 1007, 3819 948, 3911 946, 3932 1022, 3973 992, 4014 1049, 4095 991, 4138 1041, 4182 1040, 4225 937, 4265 1041, 4346 944, 4381 943, 4398 1016, 4430 1010, 4461 987, 4492 931, 4514 940, 4537 974, 4559 925, 4607 1094, 4703 949, 4782 999, 4821 1030, 4840 963, 4859 1044, 4879 1012, 4981 927, 5018 926, 5036 1022, 5098 1002, 5130 946, 5204 1019, 5231 1043, 5285 1102, 5359 1117, 5401 993, 5444 939, 5487 969, 5552 1155, 5591 962, 5669 1143, 5761 1008, 5807 1089, 5870 1173, 5941 1066, 5977 1024, 6031 1088, 6058 1089, 6176 1031, 6282 985, 6309 1029, 6337 1101, 6364 1043, 6435 1032, 6470 999, 6527 1155, 6611 1182, 6645 1024, 6662 1098, 6703 1212, 6784 1093, 6805 1218, 6826 1179, 6847 1185, 6874 1213, 6900 1222, 6926 1231, 6968 1198, 7010 1168, 7052 1220, 7147 1237, 7195 1273, 7235 1307, 7275 1282, 7314 1191, 7419 1240, 7456 1326, 7493 1297, 7530 1235, 7586 1343, 7615 1306, 7714 1337, 7763 1165, 7827 1244, 7859 1336, 7884 1189, 7933 1276, 8045 1226, 8066 1329, 8086 1230, 8107 1181, 8135 1127, 8163 1306, 8191 1242, 8236 1231, 8259 1256, 8366 1326, 8413 1166, 8505 1162, 8525 1303, 8564 1216, 8619 1289, 8682 1262, 8714 1229, 8800 1211, 8844 1267, 8965 1247, 8995 1205, 9025 1236, 9055 1217, 9155 1126, 9225 1076, 9514 1004, 9374 817, 9190 762, 9155 711, 9122 827, 9088 676, 9055 693, 8965 849, 8925 713, 8884 856, 8844 750, 8757 793, 8714 813, 8650 725, 8619 764, 8600 858, 8582 875, 8564 774, 8544 871, 8505 879, 8459 753, 8366 756, 8331 768, 8295 839, 8259 775, 8213 805, 8191 868, 8107 847, 8045 756, 8008 904, 7970 715, 7933 837, 7908 887, 7859 906, 7795 853, 7763 842, 7664 888, 7615 913, 7558 887, 7530 912, 7419 797, 7384 927, 7349 838, 7314 919, 7195 902, 7099 894, 7052 762, 6926 774, 6847 711, 6784 660, 6743 804, 6662 657, 6628 652, 6611 737, 6583 641, 6555 613, 6527 597, 6508 764, 6489 616, 6470 639, 6400 684, 6364 692, 6282 739, 6246 753, 6211 687, 6176 570, 6137 584, 6097 670, 6058 731, 6004 620, 5977 561, 5906 631, 5870 740, 5849 755, 5828 734, 5807 692, 5715 682, 5669 742, 5630 623, 5552 581, 5530 702, 5509 663, 5487 631, 5359 552, 5334 632, 5310 619, 5285 598, 5258 529, 5204 541, 5179 548, 5154 628, 5130 581, 5067 507, 5036 595, 5000 611, 4981 580, 4947 621, 4913 658, 4879 607, 4821 626, 4742 632, 4703 638, 4655 670, 4559 530, 4492 513, 4398 661, 4364 676, 4346 570, 4306 661, 4225 503, 4095 580, 4055 452, 3973 579, 3952 555, 3911 461, 3865 583, 3773 650, 3633 573, 3505 577, 3459 519, 3412 629, 3365 599, 3281 530, 3247 559, 3229 599, 3171 517, 3142 536, 3008 651, 2990 517, 2956 652, 2917 659, 2839 601, 2762 569, 2723 555, 2689 548, 2655 662, 2621 572, 2575 602, 2553 480, 2529 649, 2505 602, 2481 557, 2446 674, 2375 524, 2350 615, 2325 667, 2300 632, 2242 465, 2212 456, 2187 543, 2137 596, 2046 612, 2001 633, 1977 642, 1930 554, 1847 651, 1814 548, 1748 600, 1716 503, 1685 519, 1654 521, 1622 526, 1591 709, 1559 599, 1511 555, 1487 566, 1443 661, 1356 494, 1266 645, 1226 564, 1186 554, 1146 628, 1053 639, 1007 702, 974 697, 941 638, 908 750, 856 560, 792 661, 761 635, 668 772, 619 784, 522 722, 503 622, 483 721, 464 673, 320 683, 251 739, 216 588, 186 568, 155 618, 125 562, 93 706, 62 740, 30 588, -8 589, -45 644, -82 726, -103 677, -124 700, -145 604, -183 553, -257 654, -300 588, -322 567, -342 549, -363 654, -384 695, -433 577, -483 623, -533 680, -557 574, -606 587, -632 704, -658 753, -683 753, -712 626, -768 743, -912 743, -938 650, -964 715, -990 610, -1089 716, -1138 686, -1203 746, -1236 756, -1263 626, -1290 578, -1317 544, -1343 554, -1368 676, -1394 693, -1420 715, -1446 537, -1472 526, -1500 695, -1557 703, -1602 700, -1690 599, -1779 598, -1922 585, -1949 670, -2004 704, -2035 627, -2067 571, -2099 691, -2139 623, -2159 523, -2201 644, -2244 697, -2286 600, -2320 661, -2355 573, -2389 541, -2424 600, -2458 595, -2492 654, -2635 533, -2667 568, -2699 621, -2731 716, -2810 578, -2903 547, -3005 550, -3039 666, -3056 627, -3112 627, -3140 614, -3186 753, -3279 621, -3329 596, -3428 721, -3471 591, -3493 764, -3588 644, -3635 651, -3725 574, -3764 540, -3783 651, -3891 627, -3908 587, -3926 702, -3943 542, -3970 651, -4022 610, -4056 686, -4123 518, -4196 562, -4258 592, -4289 583, -4327 656, -4365 654, -4404 522, -4485 658, -4526 590, -4667 576, -4701 480, -4769 659, -4823 610, -4953 583, -5005 676, -5027 548, -5049 605, -5071 665, -5114 613, -5135 693, -5162 725, -5216 742, -5246 689, -5277 616, -5307 593, -5366 578, -5395 689, -5473 556, -5512 724, -5553 629, -5595 651, -5636 662, -5678 646, -5721 696, -5763 647, -5811 642, -5905 570, -5993 635, -6012 585, -6052 690, -6131 637, -6183 650, -6209 729, -6269 685, -6298 539, -6326 664, -6354 603, -6401 664, -6495 577, -6525 754, -6585 582, -6604 619, -6643 670, -6699 624, -6727 617, -6870 573, -6910 591, -6950 567, -6990 631, -7039 599, -7088 598, -7137 703, -7235 695, -7260 647, -7311 699, -7329 613, -7347 692, -7365 709, -7440 709, -7478 698, -7517 735, -7557 626, -7596 719, -7730 684, -7773 650, -7860 533, -7888 562, -7917 584, -7945 532, -7996 622, -8022 663, -8115 504, -8203 727, -8247 519, -8372 557, -8397 626, -8423 587, -8449 581, -8479 705, -8509 623, -8539 615, -8679 705, -8734 599, -8804 614, -8838 807, -8864 729, -8916 807, -9064 675, -9108 734, -9197 756, -9288 641, -9329 646, -9411 800, -9460 664, -9508 671, -9556 648, -9610 650, -9648 751, -9723 678, -9768 761, -9857 690, -9906 643, -9955 816, -10003 805, -10050 788, -10096 683, -10142 664, -10184 688, -10226 737, -10268 752, -10398 620, -10418 665, -10458 814, -10494 804, -10566 761, -10625 823, -10654 628, -10681 764, -10708 690, -10736 764, -10807 707, -10826 795, -10865 716, -10922 713, -10950 631, -11041 671, -11090 733, -11139 778, -11189 690, -11253 704, -11285 589, -11329 648, -11417 587, -11557 693, -11696 634, -11638 1091))
    POLYGON ((-11164 -630, -11135 -615, -11118 -590, -11101 -631, -11054 -650, -11008 -674, -10961 -635, -10917 -636, -10829 -646, -10765 -641, -10733 -575, -10585 -567, -10555 -602, -10524 -616, -10494 -594, -10438 -566, -10410 -581, -10390 -583, -10351 -538, -10327 -574, -10304 -586, -10280 -553, -10198 -602, -10139 -586, -10110 -549, -10074 -530, -10002 -544, -9982 -544, -9942 -579, -9899 -568, -9855 -607, -9812 -550, -9686 -614, -9548 -596, -9401 -544, -9357 -569, -9268 -555, -9230 -586, -9155 -600, -9137 -617, -9118 -572, -9100 -578, -8955 -577, -8914 -535, -8832 -512, -8802 -536, -8772 -561, -8741 -567, -8697 -541, -8608 -551, -8559 -592, -8510 -588, -8460 -558, -8434 -574, -8382 -565, -8313 -591, -8279 -598, -8260 -604, -8241 -593, -8223 -604, -8176 -618, -8130 -643, -8083 -669, -7993 -680, -7916 -691, -7874 -713, -7833 -674, -7791 -643, -7703 -701, -7659 -709, -7628 -706, -7597 -656, -7566 -678, -7515 -675, -7490 -657, -7404 -684, -7361 -678, -7274 -647, -7230 -661, -7185 -695, -7140 -650, -7022 -667, -6947 -663, -6909 -683, -6855 -684, -6829 -649, -6779 -683, -6746 -680, -6713 -680, -6681 -615, -6535 -633, -6414 -643, -6367 -589, -6319 -614, -6272 -597, -6215 -672, -6187 -633, -6168 -652, -6129 -625, -6099 -649, -6039 -609, -5992 -631, -5899 -669, -5814 -692, -5793 -700, -5773 -658, -5753 -678, -5701 -689, -5675 -602, -5649 -611, -5622 -665, -5596 -616, -5576 -667, -5537 -654, -5508 -653, -5479 -634, -5449 -607, -5402 -652, -5308 -599, -5180 -663, -5056 -687, -4978 -677, -4939 -660, -4881 -673, -4851 -630, -4760 -607, -4733 -652, -4680 -634, -4636 -701, -4615 -702, -4549 -668, -4532 -739, -4515 -740, -4498 -692, -4454 -718, -4411 -762, -4367 -749, -4349 -741, -4331 -761, -4314 -703, -4280 -753, -4211 -754, -4164 -738, -4117 -687, -4070 -708, -3988 -760, -3948 -755, -3833 -721, -3771 -693, -3740 -725, -3716 -689, -3691 -709, -3667 -676, -3634 -716, -3567 -668, -3540 -662, -3487 -680, -3435 -687, -3399 -669, -3363 -643, -3327 -657, -3289 -701, -3270 -642, -3240 -678, -3210 -635, -3180 -597, -3085 -647, -3037 -609, -2994 -628, -2972 -608, -2923 -658, -2824 -640, -2777 -613, -2684 -665, -2628 -686, -2600 -670, -2566 -671, -2549 -641, -2515 -718, -2481 -715, -2447 -679, -2416 -673, -2385 -691, -2354 -638, -2328 -669, -2302 -632, -2275 -684, -2179 -653, -2132 -683, -2084 -736, -2037 -692, -1933 -651, -1830 -708, -1703 -718, -1663 -747, -1643 -723, -1548 -640, -1521 -683, -1466 -632, -1419 -678, -1371 -660, -1323 -674, -1293 -666, -1264 -720, -1234 -715, -1190 -660, -1102 -657, -1073 -682, -1016 -686, -938 -660, -861 -674, -780 -641, -715 -648, -683 -630, -584 -624, -535 -593, -456 -615, -408 -640, -360 -597, -313 -610, -284 -629, -228 -622, -150 -631, -126 -665, -77 -644, 72 -673, 134 -653, 177 -675, 199 -686, 236 -674, 310 -671, 373 -690, 486 -613, 581 -632, 672 -626, 741 -631, 775 -643, 824 -603, 872 -604, 920 -626, 978 -584, 1026 -599, 1123 -644, 1154 -666, 1186 -626, 1217 -652, 1280 -625, 1311 -637, 1329 -602, 1347 -626, 1364 -642, 1463 -651, 1555 -684, 1601 -641, 1722 -678, 1752 -735, 1782 -741, 1812 -674, 1855 -719, 1942 -693, 1991 -680, 2015 -679, 2109 -717, 2204 -727, 2237 -762, 2302 -706, 2330 -743, 2358 -711, 2386 -702, 2410 -695, 2457 -703, 2547 -729, 2592 -747, 2618 -752, 2668 -734, 2726 -753, 2756 -742, 2831 -694, 2866 -715, 2937 -721, 3008 -726, 3054 -752, 3076 -741, 3179 -707, 3256 -732, 3295 -752, 3334 -730, 3412 -714, 3429 -714, 3463 -694, 3508 -689, 3553 -703, 3598 -667, 3656 -731, 3685 -706, 3720 -754, 3737 -711, 3765 -750, 3793 -764, 3821 -715, 3961 -738, 4004 -747, 4046 -697, 4089 -744, 4135 -725, 4182 -729, 4228 -726, 4275 -764, 4367 -761, 4387 -747, 4429 -747, 4470 -725, 4551 -728, 4594 -725, 4637 -702, 4681 -730, 4721 -704, 4802 -720, 4837 -722, 4854 -689, 4885 -684, 4917 -696, 4948 -717, 4970 -713, 4992 -712, 5015 -718, 5063 -647, 5159 -713, 5237 -695, 5276 -691, 5296 -728, 5315 -698, 5334 -702, 5437 -717, 5474 -720, 5492 -686, 5554 -708, 5585 -718, 5660 -694, 5687 -705, 5741 -671, 5814 -649, 5857 -708, 5900 -713, 5943 -695, 6008 -624, 6047 -682, 6125 -609, 6217 -660, 6263 -631, 6326 -595, 6397 -638, 6433 -647, 6487 -629, 6513 -616, 6632 -644, 6737 -658, 6765 -646, 6793 -617, 6820 -636, 6891 -663, 6926 -649, 6983 -587, 7066 -565, 7101 -627, 7118 -589, 7158 -553, 7240 -579, 7261 -544, 7282 -542, 7303 -528, 7329 -530, 7355 -512, 7382 -511, 7424 -507, 7465 -519, 7507 -495, 7603 -480, 7651 -467, 7691 -455, 7730 -462, 7770 -475, 7875 -463, 7912 -429, 7949 -451, 7986 -470, 8042 -429, 8070 -434, 8169 -442, 8219 -498, 8283 -486, 8315 -433, 8340 -486, 8388 -468, 8501 -479, 8521 -424, 8542 -474, 8563 -487, 8591 -519, 8619 -465, 8647 -477, 8692 -487, 8714 -467, 8822 -458, 8868 -504, 8961 -504, 8980 -456, 9020 -484, 9074 -462, 9138 -466, 9169 -492, 9256 -499, 9299 -486, 9421 -511, 9451 -530, 9481 -519, 9511 -516, 9611 -561, 9680 -576, 9812 -601, 9754 -671, 9646 -671, 9611 -726, 9578 -674, 9544 -719, 9511 -708, 9421 -650, 9380 -676, 9340 -635, 9299 -674, 9213 -643, 9169 -642, 9106 -654, 9074 -648, 9056 -610, 9038 -596, 9020 -646, 9000 -615, 8961 -608, 8915 -631, 8822 -662, 8786 -657, 8750 -624, 8714 -661, 8669 -612, 8647 -611, 8563 -617, 8501 -649, 8463 -598, 8426 -657, 8388 -624, 8364 -590, 8315 -593, 8251 -622, 8219 -618, 8120 -582, 8070 -574, 8014 -586, 7986 -582, 7875 -617, 7840 -567, 7805 -598, 7770 -588, 7651 -597, 7555 -607, 7507 -673, 7382 -682, 7303 -712, 7240 -745, 7199 -690, 7118 -756, 7083 -752, 7066 -722, 7039 -764, 7011 -776, 6983 -794, 6964 -730, 6945 -784, 6926 -792, 6855 -772, 6820 -770, 6737 -755, 6702 -752, 6667 -777, 6632 -804, 6592 -794, 6553 -770, 6513 -755, 6460 -789, 6433 -820, 6362 -768, 6326 -761, 6305 -759, 6284 -760, 6263 -786, 6171 -773, 6125 -755, 6086 -800, 6008 -825, 5986 -784, 5964 -793, 5943 -819, 5814 -858, 5790 -832, 5765 -829, 5741 -853, 5714 -863, 5660 -861, 5635 -848, 5610 -816, 5585 -853, 5523 -882, 5492 -841, 5455 -830, 5437 -851, 5403 -835, 5369 -819, 5334 -863, 5276 -840, 5198 -820, 5159 -820, 5111 -797, 5015 -860, 4948 -871, 4854 -819, 4819 -812, 4802 -861, 4762 -822, 4681 -897, 4551 -893, 4510 -930, 4429 -892, 4408 -911, 4367 -951, 4321 -894, 4228 -855, 4089 -872, 3961 -876, 3914 -894, 3868 -865, 3821 -881, 3737 -910, 3702 -888, 3685 -874, 3627 -868, 3598 -874, 3463 -838, 3446 -883, 3412 -844, 3373 -846, 3295 -877, 3217 -880, 3179 -888, 3145 -881, 3111 -840, 3076 -879, 3031 -870, 3008 -938, 2985 -852, 2961 -865, 2937 -882, 2902 -830, 2831 -897, 2806 -857, 2781 -845, 2756 -874, 2697 -936, 2668 -913, 2643 -899, 2592 -862, 2502 -857, 2457 -853, 2433 -835, 2386 -866, 2302 -848, 2270 -875, 2204 -874, 2172 -895, 2141 -877, 2109 -864, 2078 -863, 2046 -797, 2015 -833, 1967 -840, 1942 -836, 1899 -813, 1812 -912, 1722 -832, 1682 -855, 1641 -854, 1601 -831, 1509 -816, 1463 -791, 1430 -774, 1397 -807, 1364 -756, 1311 -828, 1248 -787, 1217 -796, 1123 -733, 1075 -730, 978 -757, 958 -784, 939 -754, 920 -773, 775 -778, 707 -752, 672 -818, 642 -822, 611 -816, 581 -838, 549 -775, 517 -760, 486 -809, 448 -825, 411 -803, 373 -787, 352 -797, 331 -793, 310 -825, 273 -820, 199 -801, 155 -815, 134 -837, 113 -843, 93 -812, 72 -800, 22 -826, -27 -804, -77 -788, -102 -833, -150 -809, -176 -754, -202 -735, -228 -753, -256 -784, -313 -762, -456 -754, -482 -774, -508 -764, -535 -795, -633 -735, -683 -763, -748 -749, -780 -754, -807 -808, -834 -812, -861 -839, -887 -826, -912 -803, -938 -793, -964 -794, -990 -837, -1016 -866, -1045 -814, -1102 -799, -1146 -790, -1234 -840, -1323 -847, -1466 -835, -1494 -796, -1548 -798, -1580 -838, -1611 -847, -1643 -827, -1683 -834, -1703 -876, -1745 -826, -1788 -797, -1830 -839, -1865 -826, -1899 -837, -1933 -850, -1968 -834, -2002 -831, -2037 -818, -2179 -872, -2211 -849, -2243 -814, -2275 -792, -2354 -841, -2447 -849, -2549 -858, -2583 -799, -2600 -822, -2656 -804, -2684 -803, -2731 -762, -2824 -803, -2873 -791, -2972 -754, -3016 -798, -3037 -741, -3132 -783, -3180 -796, -3270 -846, -3308 -852, -3327 -808, -3435 -818, -3452 -817, -3470 -786, -3487 -859, -3514 -812, -3567 -846, -3600 -819, -3667 -877, -3740 -869, -3802 -858, -3833 -866, -3871 -848, -3910 -834, -3948 -888, -4029 -841, -4070 -877, -4211 -873, -4245 -908, -4314 -850, -4367 -854, -4498 -858, -4549 -824, -4571 -849, -4593 -845, -4615 -809, -4658 -840, -4680 -796, -4706 -770, -4760 -763, -4791 -765, -4821 -786, -4851 -813, -4910 -810, -4939 -783, -5017 -834, -5056 -774, -5098 -795, -5139 -795, -5180 -781, -5223 -776, -5265 -761, -5308 -800, -5355 -780, -5449 -816, -5537 -797, -5557 -815, -5596 -771, -5675 -801, -5727 -792, -5753 -780, -5814 -803, -5842 -844, -5870 -805, -5899 -825, -5945 -796, -6039 -824, -6069 -757, -6129 -813, -6148 -782, -6187 -786, -6243 -811, -6272 -803, -6414 -815, -6454 -822, -6495 -811, -6535 -788, -6583 -801, -6632 -792, -6681 -771, -6779 -779, -6804 -806, -6855 -792, -6873 -821, -6891 -792, -6909 -789, -6985 -779, -7022 -780, -7062 -753, -7101 -791, -7140 -779, -7274 -802, -7317 -814, -7404 -864, -7432 -869, -7461 -860, -7490 -861, -7540 -825, -7566 -825, -7659 -882, -7747 -784, -7791 -858, -7916 -852, -7942 -808, -7967 -813, -7993 -821, -8023 -780, -8053 -799, -8083 -803, -8223 -771, -8279 -779, -8348 -770, -8382 -698, -8408 -723, -8460 -687, -8608 -726, -8653 -702, -8741 -696, -8832 -760, -8873 -745, -8955 -688, -9004 -730, -9052 -750, -9100 -744, -9155 -764, -9192 -710, -9268 -742, -9312 -694, -9401 -734, -9450 -744, -9499 -679, -9548 -698, -9594 -698, -9640 -744, -9686 -758, -9728 -753, -9770 -735, -9812 -731, -9942 -756, -9962 -740, -10002 -681, -10038 -674, -10110 -694, -10169 -677, -10198 -768, -10226 -721, -10253 -744, -10280 -706, -10351 -727, -10371 -700, -10410 -731, -10466 -725, -10494 -759, -10585 -751, -10634 -732, -10683 -711, -10733 -768, -10797 -763, -10829 -791, -10873 -782, -10961 -819, -11101 -775, -11182 -792, -11164 -630))
    """

    p_wkt = 'POLYGON ((-29.42 212.44, 17.20 287.43, 34.41 298.82, 51.61 221.98, 98.21 203.83, 144.81 92.32, 191.42 194.15, 235.33 216.73, 323.15 142.19, 387.49 134.29, 419.66 300.22, 567.66 307.79, 597.81 182.35, 627.96 164.08, 658.11 199.24, 714.58 311.40, 742.81 232.82, 762.26 327.99, 801.16 330.77, 824.96 257.81, 848.77 256.33, 872.57 331.43, 954.05 177.93, 1013.00 200.81, 1042.47 302.44, 1078.37 361.84, 1150.16 294.82, 1170.23 337.87, 1210.37 230.46, 1253.70 321.73, 1297.03 188.93, 1340.35 325.29, 1466.21 186.59, 1604.85 176.78, 1751.08 301.96, 1795.67 230.26, 1884.86 277.87, 1922.49 240.58, 1997.74 206.38, 2015.86 180.14, 2033.98 263.40, 2052.10 308.77, 2196.98 227.49, 2237.98 312.79, 2319.96 356.17, 2350.31 292.22, 2380.66 249.28, 2411.01 216.29, 2455.40 341.12, 2544.18 287.95, 2593.50 176.83, 2642.82 184.41, 2692.14 276.05, 2718.08 275.26, 2769.96 281.54, 2839.24 244.27, 2873.88 220.17, 2892.42 286.40, 2910.96 310.27, 2929.50 273.09, 2976.02 247.09, 3022.53 198.87, 3069.05 101.41, 3159.36 113.55, 3236.47 113.81, 3278.18 65.26, 3319.89 195.02, 3361.61 219.01, 3449.42 78.44, 3493.33 82.48, 3524.40 135.68, 3555.47 222.40, 3586.55 215.18, 3637.44 170.28, 3662.88 203.31, 3748.62 155.93, 3791.85 182.05, 3878.31 195.15, 3922.87 172.60, 3967.42 86.46, 4011.98 171.47, 4130.14 127.08, 4205.47 143.17, 4243.13 87.17, 4297.62 115.06, 4322.95 223.00, 4373.62 94.19, 4406.30 86.17, 4438.98 82.32, 4471.67 263.36, 4617.87 219.95, 4737.95 189.84, 4785.58 272.02, 4833.21 246.66, 4880.83 295.24, 4937.38 147.37, 4965.65 196.90, 4984.81 123.51, 5023.12 233.56, 5053.17 220.47, 5113.25 277.95, 5160.10 253.55, 5253.80 157.13, 5338.70 97.81, 5359.01 71.52, 5379.33 206.18, 5399.64 81.68, 5451.55 81.97, 5477.51 287.15, 5503.75 241.05, 5529.99 102.33, 5556.23 217.23, 5575.97 124.37, 5615.44 109.91, 5644.63 129.37, 5673.82 169.82, 5703.01 299.95, 5750.25 163.37, 5844.73 296.80, 5972.19 110.44, 6095.99 81.16, 6174.11 104.65, 6213.18 156.80, 6271.86 112.84, 6301.21 209.93, 6392.13 260.84, 6419.06 211.76, 6472.92 256.19, 6516.05 112.62, 6537.61 62.95, 6603.50 208.43, 6620.60 24.48, 6637.70 46.99, 6654.81 181.41, 6698.31 149.20, 6741.81 10.49, 6785.31 41.70, 6803.16 53.00, 6821.00 9.80, 6838.85 157.73, 6872.89 40.43, 6940.98 19.24, 6988.21 71.78, 7035.43 196.87, 7082.65 140.15, 7164.01 22.65, 7204.68 20.68, 7319.05 59.96, 7381.38 176.11, 7412.55 59.94, 7436.78 171.10, 7461.01 138.81, 7485.24 174.23, 7518.77 113.98, 7585.82 201.46, 7612.22 206.16, 7665.02 139.60, 7717.42 93.36, 7753.39 152.03, 7789.36 187.50, 7825.33 192.78, 7863.59 69.12, 7882.72 163.00, 7912.78 114.33, 7942.83 238.98, 7972.89 295.53, 8067.59 137.82, 8114.94 229.80, 8158.60 175.10, 8180.42 208.77, 8229.89 139.87, 8328.82 180.89, 8375.31 271.96, 8468.29 129.79, 8524.39 87.01, 8552.44 168.46, 8586.13 159.49, 8602.98 238.67, 8637.13 80.45, 8671.29 90.91, 8705.44 206.73, 8736.28 187.97, 8767.12 135.85, 8797.97 210.79, 8824.33 137.02, 8850.69 250.41, 8877.06 123.71, 8973.16 248.83, 9020.74 223.73, 9068.32 32.78, 9115.91 147.68, 9218.97 227.69, 9322.12 95.86, 9449.62 64.70, 9489.60 26.82, 9509.59 50.20, 9604.37 231.01, 9631.59 123.33, 9686.04 236.14, 9733.76 183.66, 9781.49 215.66, 9829.22 185.08, 9858.96 203.05, 9888.69 80.47, 9918.42 69.80, 9962.55 189.82, 10050.81 233.34, 10079.34 156.30, 10136.42 127.20, 10214.48 228.09, 10290.94 106.78, 10372.26 178.16, 10437.30 148.34, 10469.81 184.57, 10568.55 214.22, 10617.91 271.13, 10696.45 256.79, 10744.27 164.47, 10792.09 276.44, 10839.91 247.89, 10868.17 265.52, 10924.71 238.31, 11002.24 181.80, 11026.58 152.38, 11075.25 219.15, 11224.63 161.72, 11286.29 217.98, 11329.40 165.79, 11350.95 91.76, 11388.22 164.03, 11462.76 154.01, 11525.77 76.53, 11638.09 287.64, 11733.10 256.60, 11824.50 232.73, 11893.39 200.44, 11927.84 143.76, 11975.98 221.29, 12024.12 259.12, 12072.27 182.69, 12130.15 307.41, 12178.69 260.05, 12275.78 138.24, 12306.89 113.15, 12338.00 225.48, 12369.11 147.07, 12432.17 261.66, 12463.70 201.31, 12481.32 267.17, 12498.93 231.43, 12516.55 159.49, 12615.12 221.71, 12707.53 135.17, 12753.74 230.59, 12874.06 181.60, 12904.15 63.84, 12934.23 35.96, 12964.32 193.16, 13007.82 59.29, 13094.84 97.58, 13143.14 150.78, 13167.29 198.45, 13261.75 66.35, 13356.15 71.81, 13389.06 35.12, 13454.90 122.36, 13482.78 68.19, 13510.67 149.66, 13538.56 121.14, 13562.02 159.88, 13608.94 157.99, 13699.52 111.22, 13744.81 60.19, 13770.06 80.92, 13820.57 132.36, 13878.82 69.91, 13907.94 108.06, 13983.43 172.60, 14018.72 140.43, 14089.30 138.06, 14160.86 130.78, 14206.21 81.85, 14228.89 75.11, 14331.26 166.54, 14408.42 142.49, 14447.00 41.47, 14486.04 99.15, 14564.14 103.00, 14581.40 117.38, 14615.92 132.94, 14660.63 190.95, 14705.34 108.35, 14750.04 202.06, 14808.34 72.35, 14837.49 166.34, 14872.06 31.72, 14889.35 172.21, 14917.34 105.90, 14945.33 70.12, 14973.33 143.27, 15113.51 69.88, 15156.13 27.71, 15198.74 166.60, 15241.36 63.95, 15287.86 97.64, 15334.36 118.70, 15380.86 128.44, 15426.93 69.11, 15519.07 67.16, 15539.87 143.16, 15581.48 112.88, 15622.13 169.87, 15703.42 111.55, 15746.65 161.66, 15789.87 160.78, 15833.10 58.13, 15873.56 161.81, 15954.48 64.61, 15989.24 63.82, 16006.62 137.02, 16037.85 130.83, 16069.08 107.88, 16100.31 52.40, 16122.55 60.60, 16144.79 94.89, 16167.03 46.10, 16215.18 215.01, 16311.48 70.25, 16389.73 119.79, 16428.86 150.81, 16448.18 83.79, 16467.49 164.75, 16486.81 133.00, 16589.45 47.57, 16626.01 46.95, 16644.29 143.31, 16706.59 123.44, 16737.74 67.06, 16812.44 140.39, 16839.41 163.89, 16893.34 222.58, 16966.91 237.91, 17009.60 114.27, 17052.29 60.39, 17094.98 90.39, 17160.18 275.61, 17199.13 83.12, 17277.03 263.97, 17369.35 128.89, 17415.51 210.10, 17478.67 293.65, 17549.63 187.14, 17585.11 144.70, 17638.94 209.41, 17665.86 209.54, 17784.29 152.24, 17889.70 105.74, 17917.31 150.46, 17944.93 221.96, 17972.55 164.38, 18043.04 152.56, 18078.29 119.74, 18135.42 275.59, 18218.79 303.49, 18252.98 145.14, 18270.08 218.73, 18310.88 333.27, 18392.48 214.02, 18413.55 338.60, 18434.62 300.02, 18455.69 305.55, 18481.78 334.18, 18507.86 342.76, 18533.95 352.28, 18575.93 318.64, 18617.92 288.74, 18659.90 340.63, 18755.48 357.51, 18803.27 393.56, 18843.00 427.94, 18882.72 403.07, 18922.45 311.55, 19026.96 360.53, 19063.99 446.98, 19101.03 417.58, 19138.06 356.24, 19194.56 463.72, 19222.80 426.86, 19321.74 458.01, 19371.21 286.26, 19435.45 364.88, 19467.56 457.23, 19491.95 309.93, 19540.72 396.74, 19653.33 346.86, 19673.89 450.01, 19694.46 350.71, 19715.03 302.04, 19743.06 247.88, 19771.09 426.81, 19799.12 362.73, 19844.22 351.84, 19866.77 376.95, 19974.69 447.38, 20020.83 286.88, 20113.12 282.81, 20132.82 424.06, 20172.22 336.94, 20226.92 410.48, 20290.11 382.76, 20321.71 350.44, 20408.40 331.66, 20451.74 388.33, 20573.39 367.61, 20603.33 325.57, 20633.27 356.91, 20663.21 337.78, 20763.37 247.08, 20832.75 197.39, 21121.90 124.76, 20982.19 -61.58, 20798.06 -116.86, 20763.37 -168.47, 20729.98 -52.33, 20696.60 -203.07, 20663.21 -186.00, 20573.39 -30.02, 20532.84 -165.95, 20492.29 -22.60, 20451.74 -129.49, 20365.05 -86.09, 20321.71 -65.88, 20258.52 -154.37, 20226.92 -114.82, 20208.69 -20.49, 20190.45 -3.53, 20172.22 -105.46, 20152.52 -7.74, 20113.12 0.25, 20066.98 -125.77, 19974.69 -123.17, 19938.72 -110.93, 19902.75 -39.58, 19866.77 -104.22, 19821.67 -73.71, 19799.12 -11.04, 19715.03 -31.87, 19653.33 -123.30, 19615.79 25.12, 19578.26 -163.96, 19540.72 -41.95, 19516.33 7.66, 19467.56 26.66, 19403.33 -25.80, 19371.21 -36.82, 19272.27 9.40, 19222.80 33.66, 19166.31 8.51, 19138.06 33.31, 19026.96 -82.10, 18992.12 48.43, 18957.28 -40.73, 18922.45 40.00, 18803.27 23.34, 18707.69 15.39, 18659.90 -117.22, 18533.95 -104.93, 18455.69 -168.17, 18392.48 -219.45, 18351.68 -74.65, 18270.08 -222.31, 18235.88 -226.63, 18218.79 -141.56, 18191.00 -237.54, 18163.21 -266.47, 18135.42 -281.64, 18116.38 -114.92, 18097.34 -263.10, 18078.29 -239.75, 18007.80 -195.22, 17972.55 -186.69, 17889.70 -140.29, 17854.56 -125.94, 17819.42 -191.78, 17784.29 -309.11, 17744.81 -295.21, 17705.33 -209.14, 17665.86 -148.11, 17612.02 -258.86, 17585.11 -317.77, 17514.15 -248.24, 17478.67 -139.16, 17457.62 -124.29, 17436.56 -144.63, 17415.51 -187.00, 17323.19 -197.04, 17277.03 -136.90, 17238.08 -256.25, 17160.18 -297.68, 17138.45 -176.57, 17116.72 -215.57, 17094.98 -247.58, 16966.91 -327.14, 16942.39 -247.00, 16917.87 -259.58, 16893.34 -281.40, 16866.37 -349.49, 16812.44 -338.01, 16787.54 -331.35, 16762.64 -250.83, 16737.74 -297.81, 16675.44 -372.37, 16644.29 -283.73, 16607.73 -268.10, 16589.45 -298.79, 16555.24 -257.67, 16521.03 -220.99, 16486.81 -272.02, 16428.86 -252.74, 16350.61 -246.61, 16311.48 -240.61, 16263.33 -208.95, 16167.03 -349.02, 16100.31 -366.25, 16006.62 -218.04, 15971.86 -203.03, 15954.48 -309.36, 15914.02 -218.47, 15833.10 -375.99, 15703.42 -299.29, 15662.77 -426.94, 15581.48 -299.60, 15560.68 -324.35, 15519.07 -417.93, 15473.00 -295.77, 15380.86 -228.80, 15241.36 -305.93, 15113.51 -301.64, 15066.78 -359.88, 15020.06 -249.78, 14973.33 -280.32, 14889.35 -348.51, 14854.78 -320.13, 14837.49 -279.75, 14779.19 -361.91, 14750.04 -342.89, 14615.92 -227.53, 14598.66 -361.67, 14564.14 -227.34, 14525.09 -220.23, 14447.00 -277.92, 14369.84 -309.73, 14331.26 -323.70, 14297.14 -331.23, 14263.01 -216.72, 14228.89 -306.79, 14183.54 -276.96, 14160.86 -399.22, 14137.01 -230.28, 14113.16 -276.62, 14089.30 -321.90, 14054.01 -204.90, 13983.43 -354.91, 13958.26 -263.69, 13933.10 -211.75, 13907.94 -247.47, 13849.70 -414.12, 13820.57 -423.30, 13795.32 -335.49, 13744.81 -282.66, 13654.23 -267.05, 13608.94 -245.68, 13585.48 -237.18, 13538.56 -324.89, 13454.90 -228.26, 13421.98 -331.02, 13356.15 -278.75, 13324.68 -375.62, 13293.22 -359.74, 13261.75 -358.22, 13230.27 -353.48, 13198.78 -169.63, 13167.29 -280.16, 13118.99 -324.02, 13094.84 -312.68, 13051.33 -218.48, 12964.32 -385.06, 12874.06 -233.73, 12833.96 -315.06, 12793.85 -325.01, 12753.74 -250.98, 12661.33 -239.50, 12615.12 -177.09, 12582.26 -181.68, 12549.41 -240.73, 12516.55 -128.93, 12463.70 -318.56, 12400.64 -218.12, 12369.11 -244.16, 12275.78 -106.73, 12227.24 -95.46, 12130.15 -157.39, 12110.85 -256.63, 12091.56 -158.36, 12072.27 -206.47, 11927.84 -196.30, 11858.95 -139.87, 11824.50 -291.28, 11794.04 -311.14, 11763.57 -261.35, 11733.10 -316.75, 11701.43 -173.08, 11669.76 -139.34, 11638.09 -291.45, 11600.65 -289.67, 11563.21 -235.16, 11525.77 -152.98, 11504.77 -202.06, 11483.77 -178.54, 11462.76 -275.00, 11425.49 -325.85, 11350.95 -225.22, 11307.84 -290.65, 11286.29 -311.51, 11265.74 -329.51, 11245.18 -224.58, 11224.63 -184.14, 11174.84 -301.54, 11125.04 -255.87, 11075.25 -199.20, 11050.92 -305.18, 11002.24 -292.23, 10976.40 -174.95, 10950.56 -126.38, 10924.71 -125.61, 10896.44 -253.25, 10839.91 -136.31, 10696.45 -135.55, 10670.27 -229.40, 10644.09 -163.99, 10617.91 -269.10, 10519.18 -162.93, 10469.81 -192.65, 10404.78 -133.03, 10372.26 -123.31, 10345.16 -252.58, 10318.05 -301.38, 10290.94 -335.07, 10265.45 -325.03, 10239.97 -203.19, 10214.48 -186.23, 10188.46 -163.58, 10162.44 -342.45, 10136.42 -352.51, 10107.88 -183.70, 10050.81 -175.92, 10006.68 -179.25, 9918.42 -279.74, 9829.22 -280.74, 9686.04 -294.19, 9658.81 -208.63, 9604.37 -175.35, 9572.77 -252.10, 9541.18 -307.69, 9509.59 -187.62, 9469.61 -255.87, 9449.62 -356.34, 9407.12 -235.16, 9364.62 -182.34, 9322.12 -279.40, 9287.74 -218.25, 9253.35 -305.83, 9218.97 -338.13, 9184.62 -279.00, 9150.26 -284.47, 9115.91 -225.35, 8973.16 -345.91, 8941.12 -311.13, 8909.09 -257.95, 8877.06 -163.12, 8797.97 -301.10, 8705.44 -331.67, 8602.98 -328.96, 8569.29 -212.51, 8552.44 -251.70, 8496.34 -251.93, 8468.29 -264.59, 8421.80 -126.09, 8328.82 -258.43, 8279.36 -283.14, 8180.42 -158.14, 8136.77 -287.97, 8114.94 -115.36, 8020.24 -235.31, 7972.89 -227.80, 7882.72 -304.81, 7844.46 -339.15, 7825.33 -228.28, 7717.42 -252.27, 7699.96 -292.39, 7682.49 -177.48, 7665.02 -336.74, 7638.62 -227.55, 7585.82 -268.51, 7552.30 -193.07, 7485.24 -360.59, 7412.55 -317.34, 7350.22 -287.26, 7319.05 -296.47, 7280.93 -223.25, 7242.81 -224.58, 7204.68 -356.86, 7123.33 -220.51, 7082.65 -288.60, 6940.98 -303.01, 6906.94 -399.38, 6838.85 -220.44, 6785.31 -268.78, 6654.81 -296.00, 6603.50 -202.92, 6581.53 -331.36, 6559.57 -273.68, 6537.61 -213.73, 6494.49 -266.12, 6472.92 -186.21, 6445.99 -154.46, 6392.13 -136.71, 6361.82 -189.72, 6331.51 -263.37, 6301.21 -286.15, 6242.52 -301.34, 6213.18 -190.00, 6135.05 -323.08, 6095.99 -154.64, 6054.72 -249.85, 6013.45 -227.89, 5972.19 -217.40, 5929.70 -233.19, 5887.22 -182.62, 5844.73 -231.60, 5797.49 -237.34, 5703.01 -309.08, 5615.44 -243.66, 5595.71 -294.11, 5556.23 -189.11, 5477.51 -241.76, 5425.60 -228.72, 5399.64 -150.21, 5338.70 -193.63, 5310.40 -340.39, 5282.10 -214.98, 5253.80 -275.76, 5206.95 -214.89, 5113.25 -302.15, 5083.21 -124.65, 5023.12 -296.92, 5003.96 -259.77, 4965.65 -209.27, 4909.10 -255.40, 4880.83 -261.77, 4737.95 -306.46, 4697.92 -288.31, 4657.90 -312.02, 4617.87 -248.40, 4569.14 -279.86, 4520.40 -281.20, 4471.67 -176.00, 4373.62 -183.58, 4348.29 -232.31, 4297.62 -180.32, 4279.46 -265.88, 4261.29 -186.81, 4243.13 -169.84, 4167.80 -169.83, 4130.14 -180.81, 4090.75 -144.17, 4051.36 -253.44, 4011.98 -160.00, 3878.31 -194.88, 3835.08 -229.28, 3748.62 -346.10, 3720.04 -317.45, 3691.46 -294.93, 3662.88 -346.58, 3611.99 -256.70, 3586.55 -216.01, 3493.33 -374.62, 3405.51 -152.36, 3361.61 -359.93, 3236.47 -321.74, 3210.77 -252.68, 3185.06 -291.97, 3159.36 -297.70, 3129.25 -173.83, 3099.15 -255.86, 3069.05 -263.91, 2929.50 -174.31, 2873.88 -280.01, 2804.60 -264.58, 2769.96 -71.91, 2744.02 -150.13, 2692.14 -72.07, 2544.18 -203.82, 2499.79 -144.96, 2411.01 -122.95, 2319.96 -237.70, 2278.97 -232.95, 2196.98 -78.65, 2148.69 -214.62, 2100.39 -207.50, 2052.10 -231.17, 1997.74 -228.65, 1960.11 -128.19, 1884.86 -201.39, 1840.26 -117.72, 1751.08 -188.53, 1702.33 -235.82, 1653.59 -63.17, 1604.85 -73.79, 1558.63 -91.32, 1512.42 -196.39, 1466.21 -214.71, 1424.26 -190.51, 1382.31 -141.63, 1340.35 -127.48, 1210.37 -259.20, 1190.30 -213.70, 1150.16 -64.57, 1114.26 -74.73, 1042.47 -117.91, 983.53 -56.23, 954.05 -250.94, 926.89 -114.78, 899.73 -188.77, 872.57 -115.31, 801.16 -172.03, 781.71 -83.65, 742.81 -163.26, 686.34 -165.82, 658.11 -247.72, 567.66 -208.46, 518.32 -146.06, 468.99 -100.66, 419.66 -189.29, 355.32 -174.93, 323.15 -289.90, 279.24 -231.08, 191.42 -291.89, 51.61 -186.08, -87.40 -245.18, -29.42 212.44))'
    q_wkt = 'POLYGON ((-11.20 67.39, 17.20 82.22, 34.41 107.42, 51.61 66.80, 98.21 47.30, 144.81 23.28, 191.42 62.71, 235.33 61.16, 323.15 51.89, 387.49 56.63, 419.66 122.98, 567.66 130.54, 597.81 95.76, 627.96 82.10, 658.11 103.23, 714.58 131.77, 742.81 117.09, 762.26 114.83, 801.16 160.10, 824.96 123.17, 848.77 112.09, 872.57 145.11, 954.05 95.57, 1013.00 111.39, 1042.47 148.24, 1078.37 167.17, 1150.16 153.17, 1170.23 153.46, 1210.37 118.52, 1253.70 129.77, 1297.03 90.38, 1340.35 147.27, 1466.21 83.18, 1604.85 101.46, 1751.08 154.05, 1795.67 128.91, 1884.86 142.52, 1922.49 111.63, 1997.74 97.12, 2015.86 80.67, 2033.98 125.17, 2052.10 119.24, 2196.98 120.22, 2237.98 162.78, 2319.96 185.12, 2350.31 161.69, 2380.66 136.51, 2411.01 130.17, 2455.40 156.37, 2544.18 147.06, 2593.50 105.12, 2642.82 109.62, 2692.14 139.16, 2718.08 123.18, 2769.96 132.54, 2839.24 106.22, 2873.88 99.55, 2892.42 93.11, 2910.96 104.21, 2929.50 93.17, 2976.02 79.62, 3022.53 54.47, 3069.05 28.24, 3159.36 17.39, 3236.47 6.70, 3278.18 -15.08, 3319.89 23.98, 3361.61 54.44, 3449.42 -3.56, 3493.33 -11.43, 3524.40 -8.09, 3555.47 42.01, 3586.55 19.33, 3637.44 22.53, 3662.88 40.20, 3748.62 13.57, 3791.85 19.22, 3878.31 50.70, 3922.87 36.47, 3967.42 2.56, 4011.98 47.48, 4130.14 30.55, 4205.47 34.57, 4243.13 14.44, 4297.62 13.67, 4322.95 49.09, 4373.62 14.75, 4406.30 17.69, 4438.98 17.57, 4471.67 82.79, 4617.87 64.14, 4737.95 55.03, 4785.58 108.90, 4833.21 83.21, 4880.83 100.64, 4937.38 25.62, 4965.65 64.40, 4984.81 45.45, 5023.12 72.68, 5053.17 48.43, 5113.25 88.86, 5160.10 66.16, 5253.80 28.33, 5338.70 5.32, 5359.01 -2.55, 5379.33 39.26, 5399.64 20.03, 5451.55 8.78, 5477.51 95.82, 5503.75 86.71, 5529.99 32.80, 5556.23 82.06, 5575.97 30.66, 5615.44 43.97, 5644.63 44.31, 5673.82 63.16, 5703.01 90.89, 5750.25 45.91, 5844.73 98.82, 5972.19 34.62, 6095.99 10.61, 6174.11 20.62, 6213.18 37.86, 6271.86 24.66, 6301.21 67.42, 6392.13 90.92, 6419.06 46.04, 6472.92 63.32, 6516.05 -3.49, 6537.61 -4.42, 6603.50 29.39, 6620.60 -41.79, 6637.70 -42.61, 6654.81 5.25, 6698.31 -20.25, 6741.81 -64.75, 6785.31 -51.32, 6803.16 -43.80, 6821.00 -63.66, 6838.85 -5.50, 6872.89 -54.97, 6940.98 -56.37, 6988.21 -40.48, 7035.43 10.33, 7082.65 -10.41, 7164.01 -62.79, 7204.68 -57.34, 7319.05 -23.53, 7381.38 4.81, 7412.55 -27.04, 7436.78 8.98, 7461.01 -11.22, 7485.24 21.62, 7518.77 -18.37, 7585.82 29.20, 7612.22 35.62, 7665.02 17.37, 7717.42 10.65, 7753.39 28.41, 7789.36 54.64, 7825.33 40.61, 7863.59 -3.85, 7882.72 55.55, 7912.78 19.24, 7942.83 62.94, 7972.89 100.12, 8067.59 50.70, 8114.94 88.58, 8158.60 69.61, 8180.42 89.24, 8229.89 39.37, 8328.82 57.77, 8375.31 84.58, 8468.29 32.51, 8524.39 11.29, 8552.44 27.89, 8586.13 26.40, 8602.98 56.91, 8637.13 -20.18, 8671.29 -17.38, 8705.44 18.49, 8736.28 24.27, 8767.12 6.91, 8797.97 59.15, 8824.33 28.86, 8850.69 65.58, 8877.06 13.77, 8973.16 44.94, 9020.74 14.15, 9068.32 -38.30, 9115.91 5.50, 9218.97 46.80, 9322.12 -10.16, 9449.62 -20.46, 9489.60 -49.84, 9509.59 -25.12, 9604.37 57.98, 9631.59 14.84, 9686.04 65.13, 9733.76 19.57, 9781.49 37.59, 9829.22 23.64, 9858.96 31.63, 9888.69 -22.74, 9918.42 -17.22, 9962.55 37.74, 10050.81 40.43, 10079.34 15.24, 10136.42 11.33, 10214.48 37.37, 10290.94 23.48, 10372.26 56.13, 10437.30 49.28, 10469.81 67.87, 10568.55 73.82, 10617.91 104.78, 10696.45 82.25, 10744.27 57.69, 10792.09 100.18, 10839.91 87.76, 10868.17 68.31, 10924.71 75.13, 11002.24 66.50, 11026.58 32.68, 11075.25 53.97, 11224.63 24.69, 11286.29 44.41, 11329.40 22.34, 11350.95 11.75, 11388.22 23.32, 11462.76 26.74, 11525.77 7.40, 11638.09 84.90, 11733.10 65.18, 11824.50 71.84, 11893.39 66.55, 11927.84 54.70, 11975.98 94.26, 12024.12 93.38, 12072.27 71.33, 12130.15 113.47, 12178.69 98.18, 12275.78 53.82, 12306.89 31.11, 12338.00 71.47, 12369.11 45.29, 12432.17 72.67, 12463.70 60.16, 12481.32 95.79, 12498.93 71.38, 12516.55 56.02, 12615.12 46.84, 12707.53 13.94, 12753.74 56.42, 12874.06 19.65, 12904.15 -37.43, 12934.23 -43.78, 12964.32 23.79, 13007.82 -21.43, 13094.84 5.05, 13143.14 17.69, 13167.29 18.17, 13261.75 -18.91, 13356.15 -29.12, 13389.06 -64.55, 13454.90 -8.15, 13482.78 -45.84, 13510.67 -13.73, 13538.56 -4.03, 13562.02 2.57, 13608.94 -4.94, 13699.52 -31.27, 13744.81 -49.46, 13770.06 -54.88, 13820.57 -36.44, 13878.82 -55.38, 13907.94 -43.89, 13983.43 3.25, 14018.72 -17.62, 14089.30 -23.61, 14160.86 -28.87, 14206.21 -54.78, 14228.89 -43.22, 14331.26 -9.46, 14408.42 -34.28, 14447.00 -54.37, 14486.04 -32.52, 14564.14 -16.60, 14581.40 -16.66, 14615.92 3.82, 14660.63 8.66, 14705.34 -5.81, 14750.04 30.18, 14808.34 -33.75, 14837.49 -8.22, 14872.06 -56.31, 14889.35 -13.66, 14917.34 -52.83, 14945.33 -66.82, 14973.33 -17.76, 15113.51 -40.80, 15156.13 -49.71, 15198.74 0.78, 15241.36 -46.48, 15287.86 -27.10, 15334.36 -31.12, 15380.86 -28.33, 15426.93 -66.55, 15519.07 -63.29, 15539.87 -49.33, 15581.48 -49.54, 15622.13 -27.33, 15703.42 -30.68, 15746.65 -27.29, 15789.87 -4.38, 15833.10 -32.26, 15873.56 -6.09, 15954.48 -21.98, 15989.24 -24.02, 16006.62 8.66, 16037.85 13.31, 16069.08 1.92, 16100.31 -19.16, 16122.55 -15.17, 16144.79 -14.26, 16167.03 -20.86, 16215.18 50.78, 16311.48 -15.67, 16389.73 2.49, 16428.86 6.96, 16448.18 -30.26, 16467.49 -0.24, 16486.81 -4.26, 16589.45 -19.64, 16626.01 -22.23, 16644.29 11.40, 16706.59 -10.44, 16737.74 -20.10, 16812.44 3.45, 16839.41 -7.13, 16893.34 26.65, 16966.91 48.19, 17009.60 -10.06, 17052.29 -15.53, 17094.98 2.56, 17160.18 73.46, 17199.13 15.18, 17277.03 88.44, 17369.35 37.61, 17415.51 66.71, 17478.67 102.50, 17549.63 60.00, 17585.11 50.12, 17638.94 68.30, 17665.86 81.24, 17784.29 54.01, 17889.70 39.34, 17917.31 51.76, 17944.93 81.10, 17972.55 61.45, 18043.04 34.63, 18078.29 49.03, 18135.42 110.79, 18218.79 132.65, 18252.98 70.60, 18270.08 108.51, 18310.88 144.43, 18392.48 118.51, 18413.55 153.29, 18434.62 155.21, 18455.69 169.94, 18481.78 168.10, 18507.86 185.30, 18533.95 186.69, 18575.93 190.23, 18617.92 178.76, 18659.90 202.14, 18755.48 217.77, 18803.27 231.03, 18843.00 242.28, 18882.72 235.11, 18922.45 222.52, 19026.96 234.92, 19063.99 268.87, 19101.03 246.34, 19138.06 227.91, 19194.56 268.61, 19222.80 264.07, 19321.74 255.34, 19371.21 199.11, 19435.45 212.10, 19467.56 264.40, 19491.95 211.92, 19540.72 229.29, 19653.33 218.84, 19673.89 273.27, 19694.46 223.54, 19715.03 210.44, 19743.06 178.72, 19771.09 232.18, 19799.12 220.56, 19844.22 210.43, 19866.77 230.85, 19974.69 239.37, 20020.83 193.31, 20113.12 193.76, 20132.82 241.63, 20172.22 213.84, 20226.92 236.04, 20290.11 231.38, 20321.71 205.53, 20408.40 198.57, 20451.74 211.80, 20573.39 186.26, 20603.33 167.69, 20633.27 178.66, 20663.21 181.98, 20763.37 136.93, 20832.75 121.36, 20964.68 96.90, 20906.62 26.23, 20798.06 26.83, 20763.37 -28.22, 20729.98 23.53, 20696.60 -21.33, 20663.21 -10.88, 20573.39 47.47, 20532.84 21.63, 20492.29 62.42, 20451.74 24.03, 20365.05 54.98, 20321.71 55.32, 20258.52 43.54, 20226.92 49.77, 20208.69 87.17, 20190.45 101.55, 20172.22 52.01, 20152.52 82.85, 20113.12 89.36, 20066.98 66.39, 19974.69 35.79, 19938.72 40.45, 19902.75 73.78, 19866.77 36.52, 19821.67 85.16, 19799.12 86.43, 19715.03 80.80, 19653.33 48.77, 19615.79 99.21, 19578.26 40.95, 19540.72 73.94, 19516.33 107.69, 19467.56 104.78, 19403.33 75.44, 19371.21 79.34, 19272.27 115.57, 19222.80 123.85, 19166.31 111.86, 19138.06 115.23, 19026.96 80.93, 18992.12 131.08, 18957.28 99.61, 18922.45 109.49, 18803.27 100.91, 18707.69 90.82, 18659.90 24.63, 18533.95 15.30, 18455.69 -14.43, 18392.48 -47.11, 18351.68 7.81, 18270.08 -58.33, 18235.88 -54.59, 18218.79 -24.19, 18191.00 -65.91, 18163.21 -78.77, 18135.42 -96.82, 18116.38 -32.70, 18097.34 -86.28, 18078.29 -93.95, 18007.80 -74.66, 17972.55 -72.36, 17889.70 -57.79, 17854.56 -54.61, 17819.42 -79.50, 17784.29 -106.26, 17744.81 -96.82, 17705.33 -72.05, 17665.86 -57.12, 17612.02 -91.69, 17585.11 -122.77, 17514.15 -70.33, 17478.67 -63.49, 17457.62 -61.38, 17436.56 -62.00, 17415.51 -88.36, 17323.19 -75.21, 17277.03 -57.40, 17238.08 -102.20, 17160.18 -127.37, 17138.45 -86.74, 17116.72 -95.64, 17094.98 -121.85, 16966.91 -159.95, 16942.39 -134.48, 16917.87 -131.81, 16893.34 -155.89, 16866.37 -165.72, 16812.44 -163.03, 16787.54 -150.70, 16762.64 -118.04, 16737.74 -155.29, 16675.44 -184.03, 16644.29 -143.53, 16607.73 -132.60, 16589.45 -153.23, 16555.24 -136.98, 16521.03 -121.34, 16486.81 -165.00, 16428.86 -142.42, 16350.61 -122.46, 16311.48 -122.85, 16263.33 -99.13, 16167.03 -162.61, 16100.31 -173.28, 16006.62 -121.46, 15971.86 -114.17, 15954.48 -163.00, 15914.02 -124.32, 15833.10 -198.96, 15703.42 -195.64, 15662.77 -232.09, 15581.48 -194.21, 15560.68 -213.69, 15519.07 -253.33, 15473.00 -196.86, 15380.86 -157.63, 15241.36 -174.24, 15113.51 -178.36, 15066.78 -196.76, 15020.06 -167.31, 14973.33 -183.25, 14889.35 -212.23, 14854.78 -190.27, 14837.49 -176.66, 14779.19 -170.59, 14750.04 -176.06, 14615.92 -140.80, 14598.66 -185.22, 14564.14 -146.72, 14525.09 -148.86, 14447.00 -179.29, 14369.84 -182.25, 14331.26 -190.02, 14297.14 -183.19, 14263.01 -142.30, 14228.89 -181.62, 14183.54 -171.95, 14160.86 -240.08, 14137.01 -154.29, 14113.16 -167.66, 14089.30 -184.42, 14054.01 -132.62, 13983.43 -199.03, 13958.26 -159.89, 13933.10 -147.51, 13907.94 -176.85, 13849.70 -238.56, 13820.57 -215.33, 13795.32 -200.98, 13744.81 -164.69, 13654.23 -159.02, 13608.94 -155.02, 13585.48 -136.97, 13538.56 -167.92, 13454.90 -150.43, 13421.98 -177.69, 13356.15 -176.51, 13324.68 -197.75, 13293.22 -179.58, 13261.75 -166.28, 13230.27 -165.69, 13198.78 -99.25, 13167.29 -135.21, 13118.99 -142.25, 13094.84 -138.89, 13051.33 -115.54, 12964.32 -214.21, 12874.06 -134.02, 12833.96 -157.33, 12793.85 -156.37, 12753.74 -133.73, 12661.33 -118.15, 12615.12 -92.93, 12582.26 -76.82, 12549.41 -109.47, 12516.55 -58.85, 12463.70 -130.17, 12400.64 -89.62, 12369.11 -98.15, 12275.78 -35.72, 12227.24 -32.28, 12130.15 -59.44, 12110.85 -86.60, 12091.56 -56.57, 12072.27 -75.66, 11927.84 -80.27, 11858.95 -54.48, 11824.50 -120.32, 11794.04 -124.43, 11763.57 -118.27, 11733.10 -139.99, 11701.43 -77.33, 11669.76 -62.03, 11638.09 -111.31, 11600.65 -127.35, 11563.21 -105.89, 11525.77 -89.75, 11504.77 -99.87, 11483.77 -95.42, 11462.76 -127.63, 11425.49 -122.19, 11350.95 -102.97, 11307.84 -117.11, 11286.29 -138.91, 11265.74 -144.98, 11245.18 -113.95, 11224.63 -102.62, 11174.84 -127.94, 11125.04 -106.77, 11075.25 -90.72, 11050.92 -135.52, 11002.24 -111.85, 10976.40 -56.41, 10950.56 -37.75, 10924.71 -55.11, 10896.44 -86.54, 10839.91 -64.03, 10696.45 -56.36, 10670.27 -76.89, 10644.09 -66.47, 10617.91 -97.19, 10519.18 -37.52, 10469.81 -65.22, 10404.78 -50.90, 10372.26 -56.13, 10345.16 -110.14, 10318.05 -114.42, 10290.94 -141.40, 10265.45 -128.86, 10239.97 -104.93, 10214.48 -95.04, 10188.46 -96.80, 10162.44 -139.19, 10136.42 -168.22, 10107.88 -116.78, 10050.81 -101.82, 10006.68 -92.24, 9918.42 -142.26, 9829.22 -149.20, 9686.04 -137.55, 9658.81 -98.21, 9604.37 -100.62, 9572.77 -140.53, 9541.18 -149.25, 9509.59 -128.97, 9469.61 -136.14, 9449.62 -178.73, 9407.12 -128.67, 9364.62 -99.49, 9322.12 -140.98, 9287.74 -128.60, 9253.35 -138.91, 9218.97 -152.41, 9184.62 -136.11, 9150.26 -133.20, 9115.91 -120.17, 8973.16 -174.78, 8941.12 -151.25, 8909.09 -115.89, 8877.06 -94.60, 8797.97 -143.30, 8705.44 -150.95, 8602.98 -160.03, 8569.29 -101.43, 8552.44 -124.72, 8496.34 -106.84, 8468.29 -105.88, 8421.80 -64.49, 8328.82 -105.30, 8279.36 -93.54, 8180.42 -55.91, 8136.77 -100.57, 8114.94 -43.35, 8020.24 -84.94, 7972.89 -98.13, 7882.72 -148.62, 7844.46 -153.90, 7825.33 -110.57, 7717.42 -120.42, 7699.96 -119.09, 7682.49 -87.99, 7665.02 -161.69, 7638.62 -114.30, 7585.82 -147.98, 7552.30 -121.27, 7485.24 -179.21, 7412.55 -171.76, 7350.22 -159.95, 7319.05 -168.38, 7280.93 -149.95, 7242.81 -136.56, 7204.68 -190.77, 7123.33 -143.32, 7082.65 -179.05, 6940.98 -175.40, 6906.94 -210.25, 6838.85 -152.03, 6785.31 -156.66, 6654.81 -160.25, 6603.50 -126.54, 6581.53 -151.68, 6559.57 -147.20, 6537.61 -111.79, 6494.49 -142.76, 6472.92 -98.40, 6445.99 -72.63, 6392.13 -65.77, 6361.82 -67.77, 6331.51 -88.68, 6301.21 -115.01, 6242.52 -112.31, 6213.18 -84.89, 6135.05 -136.35, 6095.99 -76.39, 6054.72 -97.12, 6013.45 -96.92, 5972.19 -83.67, 5929.70 -78.38, 5887.22 -63.20, 5844.73 -102.61, 5797.49 -82.08, 5703.01 -118.83, 5615.44 -99.51, 5595.71 -116.94, 5556.23 -73.74, 5477.51 -102.90, 5425.60 -94.37, 5399.64 -82.56, 5338.70 -105.10, 5310.40 -146.84, 5282.10 -107.05, 5253.80 -126.93, 5206.95 -98.31, 5113.25 -126.59, 5083.21 -59.19, 5023.12 -115.85, 5003.96 -84.42, 4965.65 -88.33, 4909.10 -113.51, 4880.83 -105.00, 4737.95 -117.19, 4697.92 -124.73, 4657.90 -113.87, 4617.87 -90.48, 4569.14 -103.85, 4520.40 -94.36, 4471.67 -73.01, 4373.62 -81.49, 4348.29 -108.37, 4297.62 -94.33, 4279.46 -123.42, 4261.29 -94.79, 4243.13 -91.56, 4167.80 -81.76, 4130.14 -82.32, 4090.75 -54.91, 4051.36 -93.43, 4011.98 -80.90, 3878.31 -103.98, 3835.08 -116.15, 3748.62 -166.08, 3720.04 -170.95, 3691.46 -162.53, 3662.88 -163.76, 3611.99 -127.43, 3586.55 -127.89, 3493.33 -184.48, 3405.51 -85.90, 3361.61 -160.89, 3236.47 -153.96, 3210.77 -110.58, 3185.06 -114.93, 3159.36 -123.88, 3129.25 -82.23, 3099.15 -100.98, 3069.05 -105.33, 2929.50 -72.91, 2873.88 -81.59, 2804.60 -72.24, 2769.96 -0.46, 2744.02 -25.41, 2692.14 10.89, 2544.18 -28.10, 2499.79 -4.35, 2411.01 1.23, 2319.96 -62.06, 2278.97 -47.56, 2196.98 9.24, 2148.69 -32.32, 2100.39 -52.60, 2052.10 -46.06, 1997.74 -65.95, 1960.11 -12.40, 1884.86 -43.95, 1840.26 3.35, 1751.08 -36.78, 1702.33 -46.00, 1653.59 19.06, 1604.85 -0.03, 1558.63 -0.56, 1512.42 -46.75, 1466.21 -60.52, 1424.26 -55.27, 1382.31 -37.25, 1340.35 -33.74, 1210.37 -57.99, 1190.30 -42.89, 1150.16 16.74, 1114.26 23.53, 1042.47 3.79, 983.53 20.67, 954.05 -70.49, 926.89 -23.05, 899.73 -46.40, 872.57 -8.63, 801.16 -29.59, 781.71 -2.31, 742.81 -33.61, 686.34 -27.54, 658.11 -61.29, 567.66 -53.58, 518.32 -34.01, 468.99 -13.60, 419.66 -70.72, 355.32 -65.56, 323.15 -93.44, 279.24 -84.63, 191.42 -121.87, 51.61 -77.45, -29.93 -94.19, -11.20 67.39))'

    #tests += [test2(N, p_wkt, q_wkt, '959.406,310.225#1533.276,69.854#2404.150,242.896#1000,2000', True)]

    #3 intersection intervals
    tests += [test2(N, p_wkt, q_wkt, '959.406,310.225#1540.827,142.846#2404.150,242.896#1000,2000', True)]

    #5 intersection intervals
    tests += [test2(N, p_wkt, q_wkt, '959.406,310.225#1540.827,168.016#2404.150,242.896#1000,2000', True)]

    #POLYGON ((-11637.62 1091.43, -11590.99 1166.42, -11573.79 1177.81, -11556.59 1100.97, -11509.98 1082.82, -11463.38 971.31, -11416.78 1073.14, -11372.87 1095.72, -11285.04 1021.18, -11220.70 1013.28, -11188.53 1179.21, -11040.54 1186.78, -11010.39 1061.33, -10980.24 1043.07, -10950.09 1078.22, -10893.62 1190.38, -10865.38 1111.80, -10845.93 1206.97, -10807.04 1209.75, -10783.23 1136.80, -10759.43 1135.32, -10735.62 1210.41, -10654.14 1056.92, -10595.20 1079.79, -10565.72 1181.42, -10529.83 1240.82, -10458.03 1173.80, -10437.96 1216.86, -10397.82 1109.45, -10354.49 1200.72, -10311.17 1067.91, -10267.84 1204.28, -10141.98 1065.58, -10003.35 1055.76, -9857.12 1180.95, -9812.52 1109.24, -9723.34 1156.85, -9685.71 1119.56, -9610.45 1085.37, -9592.33 1059.13, -9574.21 1142.39, -9556.10 1187.76, -9411.21 1106.48, -9370.22 1191.77, -9288.23 1235.16, -9257.88 1171.21, -9227.54 1128.27, -9197.19 1095.28, -9152.80 1220.10, -9064.02 1166.94, -9014.70 1055.82, -8965.38 1063.39, -8916.06 1155.04, -8890.12 1154.25, -8838.24 1160.52, -8768.96 1123.26, -8734.32 1099.15, -8715.78 1165.38, -8697.23 1189.26, -8678.69 1152.07, -8632.18 1126.08, -8585.66 1077.85, -8539.14 980.40, -8448.84 992.53, -8371.72 992.80, -8330.01 944.25, -8288.30 1074.00, -8246.59 1098.00, -8158.77 957.42, -8114.87 961.47, -8083.79 1014.67, -8052.72 1101.39, -8021.65 1094.17, -7970.76 1049.27, -7945.31 1082.29, -7859.57 1034.92, -7816.34 1061.03, -7729.88 1074.13, -7685.33 1051.58, -7640.77 965.44, -7596.22 1050.45, -7478.05 1006.07, -7402.73 1022.16, -7365.07 966.15, -7310.57 994.05, -7285.24 1101.99, -7234.58 973.18, -7201.89 965.15, -7169.21 961.31, -7136.53 1142.34, -6990.32 1098.93, -6870.24 1068.83, -6822.62 1151.00, -6774.99 1125.65, -6727.36 1174.22, -6670.82 1026.35, -6642.55 1075.88, -6623.39 1002.50, -6585.07 1112.54, -6555.03 1099.46, -6494.94 1156.93, -6448.09 1132.54, -6354.39 1036.11, -6269.49 976.80, -6249.18 950.50, -6228.87 1085.17, -6208.55 960.67, -6156.64 960.96, -6130.68 1166.13, -6104.44 1120.04, -6078.20 981.32, -6051.96 1096.22, -6032.23 1003.36, -5992.75 988.90, -5963.56 1008.36, -5934.37 1048.81, -5905.18 1178.93, -5857.94 1042.35, -5763.46 1175.79, -5636.01 989.43, -5512.21 960.15, -5434.08 983.63, -5395.02 1035.79, -5336.33 991.82, -5306.99 1088.91, -5216.07 1139.83, -5189.14 1090.74, -5135.27 1135.18, -5092.15 991.61, -5070.59 941.93, -5004.70 1087.42, -4987.59 903.47, -4970.49 925.98, -4953.38 1060.40, -4909.88 1028.19, -4866.38 889.47, -4822.88 920.69, -4805.04 931.99, -4787.19 888.79, -4769.35 1036.72, -4735.30 919.42, -4667.21 898.23, -4619.99 950.77, -4572.76 1075.85, -4525.54 1019.14, -4444.19 901.64, -4403.51 899.67, -4289.14 938.95, -4226.81 1055.09, -4195.65 938.93, -4171.41 1050.09, -4147.18 1017.80, -4122.95 1053.22, -4089.42 992.96, -4022.37 1080.45, -3995.97 1085.15, -3943.18 1018.59, -3890.77 972.34, -3854.80 1031.02, -3818.83 1066.49, -3782.86 1071.77, -3744.61 948.11, -3725.48 1041.98, -3695.42 993.32, -3665.36 1117.96, -3635.30 1174.51, -3540.60 1016.81, -3493.25 1108.79, -3449.60 1054.08, -3427.77 1087.75, -3378.31 1018.86, -3279.37 1059.88, -3232.88 1150.94, -3139.90 1008.78, -3083.80 966.00, -3055.75 1047.45, -3022.06 1038.48, -3005.21 1117.65, -2971.06 959.44, -2936.91 969.90, -2902.75 1085.72, -2871.91 1066.96, -2841.07 1014.84, -2810.23 1089.78, -2783.87 1016.00, -2757.50 1129.40, -2731.14 1002.69, -2635.04 1127.81, -2587.45 1102.71, -2539.87 911.77, -2492.29 1026.67, -2389.22 1106.68, -2286.08 974.84, -2158.57 943.69, -2118.59 905.80, -2098.61 929.18, -2003.83 1109.99, -1976.60 1002.32, -1922.16 1115.13, -1874.43 1062.65, -1826.70 1094.64, -1778.97 1064.07, -1749.24 1082.04, -1719.51 959.46, -1689.77 948.78, -1645.64 1068.81, -1557.39 1112.33, -1528.85 1035.28, -1471.78 1006.19, -1393.71 1107.08, -1317.26 985.77, -1235.93 1057.14, -1170.90 1027.32, -1138.38 1063.56, -1039.65 1093.20, -990.28 1150.12, -911.74 1135.77, -863.92 1043.46, -816.11 1155.42, -768.29 1126.88, -740.02 1144.51, -683.48 1117.30, -605.95 1060.79, -581.61 1031.37, -532.94 1098.14, -383.57 1040.70, -321.90 1096.97, -278.80 1044.77, -257.24 970.74, -219.97 1043.02, -145.43 1033.00, -82.42 955.51, 29.89 1166.63, 124.91 1135.58, 216.31 1111.72, 285.20 1079.43, 319.64 1022.75, 367.79 1100.28, 415.93 1138.10, 464.07 1061.67, 521.96 1186.39, 570.50 1139.04, 667.58 1017.22, 698.70 992.13, 729.81 1104.46, 760.92 1026.05, 823.98 1140.65, 855.51 1080.30, 873.12 1146.15, 890.74 1110.41, 908.36 1038.48, 1006.92 1100.70, 1099.34 1014.16, 1145.55 1109.58, 1265.87 1060.59, 1295.95 942.82, 1326.04 914.95, 1356.12 1072.15, 1399.63 938.28, 1486.64 976.57, 1534.95 1029.77, 1559.10 1077.44, 1653.56 945.33, 1747.95 950.79, 1780.87 914.10, 1846.70 1001.34, 1874.59 947.18, 1902.48 1028.64, 1930.37 1000.13, 1953.83 1038.86, 2000.74 1036.98, 2091.33 990.21, 2136.62 939.17, 2161.87 959.91, 2212.38 1011.35, 2270.62 948.90, 2299.74 987.04, 2375.23 1051.59, 2410.52 1019.42, 2481.11 1017.05, 2552.67 1009.77, 2598.02 960.84, 2620.70 954.10, 2723.07 1045.53, 2800.22 1021.47, 2838.80 920.45, 2877.85 978.13, 2955.94 981.98, 2973.20 996.36, 3007.73 1011.92, 3052.44 1069.94, 3097.14 987.33, 3141.85 1081.05, 3200.15 951.34, 3229.30 1045.32, 3263.87 910.70, 3281.15 1051.20, 3309.15 984.89, 3337.14 949.11, 3365.13 1022.25, 3505.32 948.86, 3547.93 906.69, 3590.55 1045.59, 3633.16 942.94, 3679.66 976.62, 3726.16 997.69, 3772.67 1007.42, 3818.74 948.09, 3910.88 946.15, 3931.68 1022.15, 3973.28 991.87, 4013.93 1048.86, 4095.23 990.53, 4138.45 1040.65, 4181.68 1039.77, 4224.90 937.12, 4265.36 1040.80, 4346.29 943.60, 4381.05 942.81, 4398.42 1016.00, 4429.66 1009.82, 4460.89 986.86, 4492.12 931.39, 4514.36 939.58, 4536.60 973.88, 4558.83 925.09, 4606.99 1093.99, 4703.29 949.23, 4781.54 998.77, 4820.66 1029.79, 4839.98 962.78, 4859.30 1043.74, 4878.62 1011.98, 4981.26 926.56, 5017.82 925.94, 5036.10 1022.30, 5098.39 1002.42, 5129.54 946.05, 5204.25 1019.38, 5231.21 1042.87, 5285.15 1101.56, 5358.72 1116.90, 5401.41 993.25, 5444.10 939.38, 5486.79 969.38, 5551.99 1154.60, 5590.94 962.11, 5668.84 1142.96, 5761.16 1007.88, 5807.32 1089.09, 5870.48 1172.64, 5941.43 1066.13, 5976.91 1023.68, 6030.75 1088.40, 6057.66 1088.53, 6176.09 1031.23, 6281.50 984.73, 6309.12 1029.45, 6336.74 1100.95, 6364.35 1043.37, 6434.85 1031.54, 6470.10 998.72, 6527.23 1154.57, 6610.59 1182.48, 6644.79 1024.12, 6661.89 1097.72, 6702.69 1212.26, 6784.28 1093.00, 6805.35 1217.58, 6826.43 1179.01, 6847.50 1184.53, 6873.58 1213.17, 6899.67 1221.75, 6925.75 1231.27, 6967.74 1197.62, 7009.72 1167.73, 7051.71 1219.62, 7147.29 1236.50, 7195.07 1272.55, 7234.80 1306.93, 7274.53 1282.06, 7314.25 1190.54, 7418.76 1239.52, 7455.80 1325.97, 7492.83 1296.57, 7529.87 1235.22, 7586.36 1342.70, 7614.61 1305.84, 7713.55 1337.00, 7763.02 1165.24, 7827.25 1243.87, 7859.37 1336.22, 7883.75 1188.92, 7932.53 1275.72, 8045.13 1225.85, 8065.70 1329.00, 8086.27 1229.69, 8106.84 1181.03, 8134.87 1126.86, 8162.90 1305.80, 8190.93 1241.72, 8236.03 1230.83, 8258.58 1255.93, 8366.49 1326.36, 8412.64 1165.86, 8504.93 1161.79, 8524.63 1303.04, 8564.02 1215.93, 8618.73 1289.47, 8681.92 1261.75, 8713.51 1229.42, 8800.20 1210.65, 8843.55 1267.31, 8965.19 1246.60, 8995.13 1204.56, 9025.07 1235.89, 9055.02 1216.77, 9155.18 1126.06, 9224.56 1076.37, 9513.71 1003.75, 9373.99 817.40, 9189.87 762.12, 9155.18 710.52, 9121.79 826.66, 9088.40 675.91, 9055.02 692.99, 8965.19 848.96, 8924.64 713.03, 8884.09 856.38, 8843.55 749.50, 8756.86 792.90, 8713.51 813.11, 8650.32 724.62, 8618.73 764.17, 8600.49 858.49, 8582.26 875.46, 8564.02 773.52, 8544.32 871.25, 8504.93 879.23, 8458.78 753.22, 8366.49 755.82, 8330.52 768.05, 8294.55 839.41, 8258.58 774.76, 8213.48 805.27, 8190.93 867.95, 8106.84 847.12, 8045.13 755.69, 8007.60 904.10, 7970.06 715.03, 7932.53 837.03, 7908.14 886.65, 7859.37 905.65, 7795.14 853.18, 7763.02 842.16, 7664.08 888.38, 7614.61 912.64, 7558.12 887.50, 7529.87 912.30, 7418.76 796.89, 7383.93 927.41, 7349.09 838.25, 7314.25 918.98, 7195.07 902.33, 7099.50 894.38, 7051.71 761.77, 6925.75 774.05, 6847.50 710.81, 6784.28 659.54, 6743.48 804.34, 6661.89 656.68, 6627.69 652.36, 6610.59 737.43, 6582.80 641.44, 6555.02 612.52, 6527.23 597.35, 6508.19 764.07, 6489.14 615.88, 6470.10 639.23, 6399.60 683.76, 6364.35 692.29, 6281.50 738.70, 6246.37 753.04, 6211.23 687.20, 6176.09 569.87, 6136.62 583.77, 6097.14 669.85, 6057.66 730.88, 6003.83 620.13, 5976.91 561.21, 5905.96 630.75, 5870.48 739.82, 5849.42 754.69, 5828.37 734.36, 5807.32 691.98, 5715.00 681.95, 5668.84 742.09, 5629.89 622.73, 5551.99 581.31, 5530.25 702.42, 5508.52 663.42, 5486.79 631.41, 5358.72 551.84, 5334.20 631.99, 5309.67 619.41, 5285.15 597.59, 5258.18 529.49, 5204.25 540.98, 5179.35 547.63, 5154.44 628.15, 5129.54 581.18, 5067.25 506.62, 5036.10 595.25, 4999.54 610.88, 4981.26 580.20, 4947.05 621.31, 4912.83 658.00, 4878.62 606.97, 4820.66 626.25, 4742.41 632.37, 4703.29 638.38, 4655.14 670.04, 4558.83 529.96, 4492.12 512.74, 4398.42 660.95, 4363.67 675.95, 4346.29 569.63, 4305.83 660.52, 4224.90 503.00, 4095.23 579.69, 4054.58 452.05, 3973.28 579.39, 3952.48 554.63, 3910.88 461.05, 3864.81 583.22, 3772.67 650.19, 3633.16 573.05, 3505.32 577.35, 3458.59 519.10, 3411.86 629.21, 3365.13 598.66, 3281.15 530.47, 3246.58 558.86, 3229.30 599.23, 3171.00 517.08, 3141.85 536.10, 3007.73 651.45, 2990.47 517.31, 2955.94 651.65, 2916.90 658.76, 2838.80 601.06, 2761.64 569.26, 2723.07 555.29, 2688.94 547.75, 2654.82 662.26, 2620.70 572.20, 2575.34 602.02, 2552.67 479.77, 2528.82 648.71, 2504.96 602.37, 2481.11 557.09, 2445.82 674.09, 2375.23 524.07, 2350.07 615.30, 2324.91 667.24, 2299.74 631.51, 2241.50 464.87, 2212.38 455.68, 2187.13 543.50, 2136.62 596.32, 2046.03 611.94, 2000.74 633.30, 1977.29 641.81, 1930.37 554.10, 1846.70 650.72, 1813.79 547.97, 1747.95 600.24, 1716.49 503.37, 1685.02 519.25, 1653.56 520.77, 1622.07 525.50, 1590.58 709.35, 1559.10 598.83, 1510.79 554.96, 1486.64 566.31, 1443.14 660.51, 1356.12 493.93, 1265.87 645.26, 1225.76 563.93, 1185.65 553.97, 1145.55 628.01, 1053.13 639.49, 1006.92 701.90, 974.07 697.31, 941.21 638.26, 908.36 750.06, 855.51 560.43, 792.45 660.86, 760.92 634.82, 667.58 772.25, 619.04 783.53, 521.96 721.60, 502.66 622.35, 483.37 720.63, 464.07 672.52, 319.64 682.69, 250.75 739.12, 216.31 587.70, 185.84 567.85, 155.38 617.63, 124.91 562.23, 93.24 705.90, 61.57 739.64, 29.89 587.53, -7.55 589.31, -44.98 643.83, -82.42 726.01, -103.43 676.92, -124.43 700.44, -145.43 603.98, -182.70 553.13, -257.24 653.77, -300.35 588.33, -321.90 567.47, -342.46 549.48, -363.01 654.41, -383.57 694.84, -433.36 577.45, -483.15 623.12, -532.94 679.78, -557.28 573.81, -605.95 586.75, -631.80 704.04, -657.64 752.60, -683.48 753.38, -711.75 625.74, -768.29 742.68, -911.74 743.44, -937.92 649.59, -964.10 715.00, -990.28 609.89, -1089.01 716.06, -1138.38 686.33, -1203.41 745.95, -1235.93 755.68, -1263.04 626.40, -1290.15 577.61, -1317.26 543.92, -1342.74 553.95, -1368.23 675.79, -1393.71 692.75, -1419.73 715.40, -1445.76 536.53, -1471.78 526.48, -1500.31 695.29, -1557.39 703.06, -1601.51 699.74, -1689.77 599.24, -1778.97 598.25, -1922.16 584.80, -1949.38 670.35, -2003.83 703.64, -2035.42 626.89, -2067.01 571.29, -2098.61 691.37, -2138.58 623.11, -2158.57 522.64, -2201.07 643.83, -2243.57 696.65, -2286.08 599.58, -2320.46 660.74, -2354.84 573.16, -2389.22 540.85, -2423.58 599.99, -2457.93 594.51, -2492.29 653.63, -2635.04 533.07, -2667.07 567.86, -2699.11 621.04, -2731.14 715.87, -2810.23 577.88, -2902.75 547.31, -3005.21 550.03, -3038.91 666.48, -3055.75 627.29, -3111.85 627.06, -3139.90 614.40, -3186.39 752.90, -3279.37 620.56, -3328.84 595.85, -3427.77 720.85, -3471.42 591.02, -3493.25 763.63, -3587.95 643.68, -3635.30 651.18, -3725.48 574.18, -3763.73 539.84, -3782.86 650.71, -3890.77 626.72, -3908.24 586.59, -3925.71 701.51, -3943.18 542.25, -3969.58 651.43, -4022.37 610.48, -4055.90 685.92, -4122.95 518.40, -4195.65 561.64, -4257.98 591.72, -4289.14 582.51, -4327.27 655.74, -4365.39 654.41, -4403.51 522.12, -4484.86 658.47, -4525.54 590.38, -4667.21 575.98, -4701.25 479.61, -4769.35 658.55, -4822.88 610.21, -4953.38 582.98, -5004.70 676.07, -5026.66 547.63, -5048.62 605.30, -5070.59 665.25, -5113.71 612.86, -5135.27 692.78, -5162.20 724.52, -5216.07 742.28, -5246.37 689.27, -5276.68 615.61, -5306.99 592.84, -5365.67 577.65, -5395.02 688.99, -5473.14 555.91, -5512.21 724.35, -5553.47 629.14, -5594.74 651.09, -5636.01 661.59, -5678.49 645.79, -5720.98 696.37, -5763.46 647.38, -5810.70 641.65, -5905.18 569.91, -5992.75 635.32, -6012.49 584.88, -6051.96 689.88, -6130.68 637.23, -6182.60 650.27, -6208.55 728.78, -6269.49 685.35, -6297.79 538.60, -6326.09 664.00, -6354.39 603.23, -6401.24 664.09, -6494.94 576.83, -6524.99 754.34, -6585.07 582.07, -6604.23 619.22, -6642.55 669.72, -6699.09 623.59, -6727.36 617.22, -6870.24 572.52, -6910.27 590.68, -6950.30 566.97, -6990.32 630.59, -7039.06 599.12, -7087.79 597.79, -7136.53 702.99, -7234.58 695.41, -7259.91 646.68, -7310.57 698.66, -7328.74 613.10, -7346.90 692.18, -7365.07 709.15, -7440.39 709.15, -7478.05 698.18, -7517.44 734.82, -7556.83 625.55, -7596.22 718.98, -7729.88 684.10, -7773.11 649.71, -7859.57 532.89, -7888.15 561.54, -7916.73 584.06, -7945.31 532.40, -7996.20 622.29, -8021.65 662.98, -8114.87 504.37, -8202.68 726.63, -8246.59 519.06, -8371.72 557.25, -8397.43 626.31, -8423.13 587.01, -8448.84 581.28, -8478.94 705.16, -8509.04 623.13, -8539.14 615.07, -8678.69 704.68, -8734.32 598.98, -8803.60 614.41, -8838.24 807.08, -8864.18 728.85, -8916.06 806.92, -9064.02 675.17, -9108.41 734.03, -9197.19 756.03, -9288.23 641.29, -9329.22 646.03, -9411.21 800.34, -9459.50 664.37, -9507.80 671.49, -9556.10 647.82, -9610.45 650.34, -9648.08 750.80, -9723.34 677.60, -9767.93 761.26, -9857.12 690.45, -9905.86 643.16, -9954.61 815.81, -10003.35 805.19, -10049.56 787.67, -10095.77 682.59, -10141.98 664.28, -10183.94 688.47, -10225.89 737.35, -10267.84 751.51, -10397.82 619.79, -10417.89 665.29, -10458.03 814.42, -10493.93 804.26, -10565.72 761.08, -10624.67 822.75, -10654.14 628.04, -10681.30 764.21, -10708.46 690.22, -10735.62 763.67, -10807.04 706.95, -10826.48 795.34, -10865.38 715.72, -10921.85 713.17, -10950.09 631.27, -11040.54 670.52, -11089.87 732.93, -11139.20 778.33, -11188.53 689.70, -11252.87 704.06, -11285.04 589.09, -11328.95 647.90, -11416.78 587.10, -11556.59 692.91, -11695.60 633.80, -11637.62 1091.43))
    #POLYGON ((-11163.62 -630.21, -11135.22 -615.38, -11118.02 -590.19, -11100.81 -630.81, -11054.21 -650.31, -11007.61 -674.33, -10961.01 -634.89, -10917.10 -636.45, -10829.27 -645.72, -10764.93 -640.98, -10732.76 -574.63, -10584.77 -567.07, -10554.62 -601.84, -10524.47 -615.51, -10494.32 -594.37, -10437.85 -565.84, -10409.61 -580.52, -10390.16 -582.78, -10351.27 -537.51, -10327.46 -574.44, -10303.66 -585.52, -10279.85 -552.50, -10198.37 -602.04, -10139.43 -586.22, -10109.95 -549.37, -10074.06 -530.44, -10002.26 -544.43, -9982.19 -544.14, -9942.05 -579.09, -9898.72 -567.84, -9855.40 -607.22, -9812.07 -550.34, -9686.21 -614.43, -9547.58 -596.15, -9401.35 -543.56, -9356.75 -568.70, -9267.57 -555.09, -9229.94 -585.97, -9154.68 -600.49, -9136.56 -616.94, -9118.44 -572.44, -9100.32 -578.37, -8955.44 -577.39, -8914.45 -534.82, -8832.46 -512.48, -8802.11 -535.92, -8771.76 -561.09, -8741.42 -567.44, -8697.03 -541.24, -8608.25 -550.54, -8558.93 -592.48, -8509.61 -587.99, -8460.29 -558.45, -8434.35 -574.43, -8382.46 -565.06, -8313.19 -591.39, -8278.55 -598.06, -8260.01 -604.50, -8241.46 -593.40, -8222.92 -604.44, -8176.40 -617.99, -8129.89 -643.14, -8083.37 -669.37, -7993.07 -680.21, -7915.95 -690.90, -7874.24 -712.69, -7832.53 -673.63, -7790.82 -643.17, -7703.00 -701.17, -7659.09 -709.04, -7628.02 -705.69, -7596.95 -655.59, -7565.88 -678.28, -7514.99 -675.08, -7489.54 -657.41, -7403.80 -684.04, -7360.57 -678.38, -7274.11 -646.91, -7229.56 -661.14, -7185.00 -695.05, -7140.45 -650.13, -7022.28 -667.06, -6946.96 -663.04, -6909.30 -683.17, -6854.80 -683.94, -6829.47 -648.51, -6778.81 -682.86, -6746.12 -679.92, -6713.44 -680.04, -6680.76 -614.82, -6534.55 -633.47, -6414.47 -642.58, -6366.85 -588.71, -6319.22 -614.40, -6271.59 -596.97, -6215.05 -671.99, -6186.78 -633.20, -6167.62 -652.15, -6129.30 -624.93, -6099.26 -649.18, -6039.17 -608.75, -5992.32 -631.45, -5898.62 -669.27, -5813.72 -692.28, -5793.41 -700.16, -5773.10 -658.35, -5752.78 -677.58, -5700.87 -688.82, -5674.91 -601.79, -5648.67 -610.90, -5622.43 -664.81, -5596.19 -615.55, -5576.46 -666.94, -5536.98 -653.64, -5507.79 -653.30, -5478.60 -634.45, -5449.41 -606.72, -5402.17 -651.70, -5307.69 -598.79, -5180.24 -662.99, -5056.44 -687.00, -4978.31 -676.99, -4939.25 -659.75, -4880.56 -672.95, -4851.22 -630.18, -4760.30 -606.69, -4733.37 -651.57, -4679.50 -634.29, -4636.38 -701.10, -4614.81 -702.03, -4548.93 -668.22, -4531.82 -739.40, -4514.72 -740.21, -4497.61 -692.36, -4454.11 -717.86, -4410.61 -762.36, -4367.11 -748.93, -4349.27 -741.41, -4331.42 -761.27, -4313.58 -703.11, -4279.53 -752.58, -4211.44 -753.98, -4164.22 -738.08, -4116.99 -687.28, -4069.77 -708.01, -3988.42 -760.40, -3947.74 -754.95, -3833.37 -721.14, -3771.04 -692.80, -3739.88 -724.65, -3715.64 -688.63, -3691.41 -708.82, -3667.18 -675.99, -3633.65 -715.98, -3566.60 -668.41, -3540.20 -661.99, -3487.41 -680.23, -3435.00 -686.95, -3399.03 -669.20, -3363.06 -642.96, -3327.09 -657.00, -3288.83 -701.46, -3269.71 -642.06, -3239.65 -678.37, -3209.59 -634.67, -3179.53 -597.49, -3084.83 -646.90, -3037.48 -609.03, -2993.83 -628.00, -2972.00 -608.37, -2922.53 -658.24, -2823.60 -639.83, -2777.11 -613.03, -2684.13 -665.09, -2628.03 -686.32, -2599.98 -669.72, -2566.29 -671.20, -2549.44 -640.70, -2515.29 -717.79, -2481.14 -714.99, -2446.98 -679.12, -2416.14 -673.34, -2385.30 -690.70, -2354.46 -638.45, -2328.10 -668.74, -2301.73 -632.03, -2275.37 -683.83, -2179.27 -652.67, -2131.68 -683.46, -2084.10 -735.91, -2036.52 -692.11, -1933.45 -650.81, -1830.31 -707.76, -1702.80 -718.07, -1662.82 -747.44, -1642.84 -722.72, -1548.06 -639.62, -1520.83 -682.76, -1466.39 -632.48, -1418.66 -678.03, -1370.93 -660.02, -1323.20 -673.97, -1293.47 -665.98, -1263.73 -720.35, -1234.00 -714.83, -1189.87 -659.87, -1101.61 -657.18, -1073.08 -682.36, -1016.01 -686.28, -937.94 -660.24, -861.49 -674.13, -780.16 -641.48, -715.13 -648.33, -682.61 -629.74, -583.88 -623.78, -534.51 -592.83, -455.97 -615.35, -408.15 -639.92, -360.34 -597.42, -312.52 -609.85, -284.25 -629.30, -227.71 -622.48, -150.18 -631.11, -125.84 -664.93, -77.17 -643.63, 72.20 -672.91, 133.87 -653.20, 176.98 -675.27, 198.53 -685.86, 235.80 -674.29, 310.34 -670.87, 373.35 -690.21, 485.66 -612.70, 580.68 -632.43, 672.08 -625.77, 740.97 -631.05, 775.41 -642.91, 823.56 -603.35, 871.70 -604.23, 919.84 -626.28, 977.73 -584.14, 1026.27 -599.43, 1123.35 -643.78, 1154.47 -666.50, 1185.58 -626.14, 1216.69 -652.32, 1279.75 -624.94, 1311.28 -637.45, 1328.89 -601.82, 1346.51 -626.23, 1364.13 -641.59, 1462.69 -650.76, 1555.11 -683.67, 1601.32 -641.19, 1721.64 -677.96, 1751.72 -735.03, 1781.81 -741.39, 1811.89 -673.82, 1855.40 -719.04, 1942.41 -692.55, 1990.72 -679.92, 2014.87 -679.43, 2109.33 -716.51, 2203.72 -726.73, 2236.64 -762.16, 2302.47 -705.76, 2330.36 -743.45, 2358.25 -711.34, 2386.14 -701.63, 2409.60 -695.04, 2456.52 -702.54, 2547.10 -728.88, 2592.39 -747.06, 2617.64 -752.49, 2668.15 -734.05, 2726.39 -752.99, 2755.52 -741.50, 2831.00 -694.36, 2866.29 -715.23, 2936.88 -721.21, 3008.44 -726.47, 3053.79 -752.38, 3076.47 -740.83, 3178.84 -707.07, 3255.99 -731.89, 3294.57 -751.98, 3333.62 -730.13, 3411.71 -714.21, 3428.97 -714.27, 3463.50 -693.79, 3508.21 -688.94, 3552.91 -703.41, 3597.62 -667.43, 3655.92 -731.35, 3685.07 -705.83, 3719.64 -753.92, 3736.92 -711.27, 3764.92 -750.44, 3792.91 -764.43, 3820.91 -715.37, 3961.09 -738.41, 4003.70 -747.32, 4046.32 -696.82, 4088.93 -744.09, 4135.43 -724.71, 4181.93 -728.73, 4228.44 -725.94, 4274.51 -764.15, 4366.65 -760.90, 4387.45 -746.94, 4429.05 -747.15, 4469.70 -724.93, 4551.00 -728.29, 4594.22 -724.90, 4637.45 -701.99, 4680.67 -729.87, 4721.14 -703.70, 4802.06 -719.59, 4836.82 -721.62, 4854.19 -688.95, 4885.43 -684.30, 4916.66 -695.69, 4947.89 -716.77, 4970.13 -712.77, 4992.37 -711.87, 5014.61 -718.46, 5062.76 -646.83, 5159.06 -713.27, 5237.31 -695.12, 5276.43 -690.65, 5295.75 -727.87, 5315.07 -697.85, 5334.39 -701.86, 5437.03 -717.25, 5473.59 -719.84, 5491.87 -686.21, 5554.16 -708.05, 5585.31 -717.71, 5660.02 -694.16, 5686.98 -704.74, 5740.92 -670.96, 5814.49 -649.42, 5857.18 -707.67, 5899.87 -713.13, 5942.56 -695.05, 6007.76 -624.15, 6046.71 -682.43, 6124.61 -609.16, 6216.93 -659.99, 6263.09 -630.89, 6326.25 -595.10, 6397.21 -637.61, 6432.68 -647.49, 6486.52 -629.31, 6513.43 -616.36, 6631.86 -643.59, 6737.27 -658.27, 6764.89 -645.85, 6792.51 -616.51, 6820.12 -636.16, 6890.62 -662.98, 6925.87 -648.58, 6983.00 -586.82, 7066.36 -564.95, 7100.56 -627.01, 7117.66 -589.10, 7158.46 -553.18, 7240.05 -579.10, 7261.12 -544.32, 7282.20 -542.40, 7303.27 -527.67, 7329.35 -529.51, 7355.44 -512.31, 7381.52 -510.92, 7423.51 -507.38, 7465.49 -518.85, 7507.48 -495.47, 7603.06 -479.83, 7650.84 -466.58, 7690.57 -455.32, 7730.30 -462.49, 7770.02 -475.09, 7874.53 -462.69, 7911.57 -428.74, 7948.60 -451.27, 7985.64 -469.70, 8042.13 -429.00, 8070.38 -433.53, 8169.32 -442.27, 8218.79 -498.49, 8283.02 -485.51, 8315.14 -433.20, 8339.52 -485.69, 8388.30 -468.32, 8500.90 -478.77, 8521.47 -424.34, 8542.04 -474.07, 8562.61 -487.16, 8590.64 -518.89, 8618.67 -465.43, 8646.70 -477.05, 8691.80 -487.18, 8714.35 -466.76, 8822.26 -458.24, 8868.41 -504.30, 8960.70 -503.85, 8980.40 -455.98, 9019.79 -483.77, 9074.50 -461.57, 9137.69 -466.22, 9169.28 -492.08, 9255.97 -499.04, 9299.32 -485.81, 9420.96 -511.34, 9450.90 -529.91, 9480.85 -518.94, 9510.79 -515.63, 9610.95 -560.68, 9680.33 -576.25, 9812.26 -600.71, 9754.20 -671.38, 9645.64 -670.78, 9610.95 -725.83, 9577.56 -674.08, 9544.17 -718.94, 9510.79 -708.49, 9420.96 -650.14, 9380.41 -675.98, 9339.87 -635.19, 9299.32 -673.58, 9212.63 -642.63, 9169.28 -642.29, 9106.09 -654.07, 9074.50 -647.84, 9056.26 -610.44, 9038.03 -596.06, 9019.79 -645.59, 9000.10 -614.75, 8960.70 -608.25, 8914.55 -631.21, 8822.26 -661.82, 8786.29 -657.16, 8750.32 -623.83, 8714.35 -661.09, 8669.25 -612.44, 8646.70 -611.18, 8562.61 -616.81, 8500.90 -648.84, 8463.37 -598.40, 8425.83 -656.66, 8388.30 -623.67, 8363.91 -589.92, 8315.14 -592.83, 8250.91 -622.17, 8218.79 -618.26, 8119.85 -582.04, 8070.38 -573.76, 8013.89 -585.75, 7985.64 -582.37, 7874.53 -616.68, 7839.70 -566.53, 7804.86 -598.00, 7770.02 -588.12, 7650.84 -596.70, 7555.27 -606.78, 7507.48 -672.98, 7381.52 -682.30, 7303.27 -712.04, 7240.05 -744.71, 7199.26 -689.79, 7117.66 -755.94, 7083.46 -752.20, 7066.36 -721.80, 7038.57 -763.52, 7010.79 -776.38, 6983.00 -794.42, 6963.96 -730.31, 6944.91 -783.89, 6925.87 -791.56, 6855.37 -772.27, 6820.12 -769.96, 6737.27 -755.39, 6702.14 -752.22, 6667.00 -777.10, 6631.86 -803.86, 6592.39 -794.43, 6552.91 -769.65, 6513.43 -754.73, 6459.60 -789.30, 6432.68 -820.38, 6361.73 -767.94, 6326.25 -761.10, 6305.19 -758.99, 6284.14 -759.61, 6263.09 -785.97, 6170.77 -772.81, 6124.61 -755.01, 6085.66 -799.81, 6007.76 -824.98, 5986.03 -784.35, 5964.29 -793.25, 5942.56 -819.45, 5814.49 -857.55, 5789.97 -832.08, 5765.44 -829.42, 5740.92 -853.50, 5713.95 -863.33, 5660.02 -860.64, 5635.12 -848.31, 5610.21 -815.64, 5585.31 -852.90, 5523.02 -881.64, 5491.87 -841.14, 5455.31 -830.20, 5437.03 -850.84, 5402.82 -834.59, 5368.60 -818.94, 5334.39 -862.60, 5276.43 -840.03, 5198.18 -820.06, 5159.06 -820.46, 5110.91 -796.74, 5014.61 -860.22, 4947.89 -870.89, 4854.19 -819.06, 4819.44 -811.78, 4802.06 -860.61, 4761.60 -821.93, 4680.67 -896.57, 4551.00 -893.25, 4510.35 -929.70, 4429.05 -891.82, 4408.25 -911.29, 4366.65 -950.94, 4320.58 -894.47, 4228.44 -855.24, 4088.93 -871.84, 3961.09 -875.97, 3914.36 -894.36, 3867.63 -864.92, 3820.91 -880.86, 3736.92 -909.83, 3702.35 -887.88, 3685.07 -874.27, 3626.77 -868.20, 3597.62 -873.67, 3463.50 -838.41, 3446.24 -882.82, 3411.71 -844.33, 3372.67 -846.47, 3294.57 -876.90, 3217.42 -879.86, 3178.84 -887.62, 3144.71 -880.79, 3110.59 -839.91, 3076.47 -879.22, 3031.11 -869.56, 3008.44 -937.69, 2984.59 -851.90, 2960.73 -865.26, 2936.88 -882.02, 2901.59 -830.23, 2831.00 -896.64, 2805.84 -857.50, 2780.68 -845.12, 2755.52 -874.46, 2697.27 -936.17, 2668.15 -912.93, 2642.90 -898.58, 2592.39 -862.30, 2501.81 -856.63, 2456.52 -852.63, 2433.06 -834.58, 2386.14 -865.53, 2302.47 -848.03, 2269.56 -875.29, 2203.72 -874.12, 2172.26 -895.36, 2140.79 -877.19, 2109.33 -863.89, 2077.84 -863.29, 2046.36 -796.86, 2014.87 -832.82, 1966.56 -839.86, 1942.41 -836.49, 1898.91 -813.14, 1811.89 -911.81, 1721.64 -831.63, 1681.53 -854.93, 1641.42 -853.98, 1601.32 -831.34, 1508.90 -815.75, 1462.69 -790.54, 1429.84 -774.43, 1396.98 -807.08, 1364.13 -756.46, 1311.28 -827.77, 1248.22 -787.23, 1216.69 -795.76, 1123.35 -733.32, 1074.81 -729.89, 977.73 -757.04, 958.43 -784.20, 939.14 -754.18, 919.84 -773.27, 775.41 -777.88, 706.52 -752.09, 672.08 -817.93, 641.61 -822.04, 611.15 -815.88, 580.68 -837.59, 549.01 -774.94, 517.34 -759.64, 485.66 -808.92, 448.23 -824.96, 410.79 -803.49, 373.35 -787.36, 352.35 -797.48, 331.34 -793.02, 310.34 -825.24, 273.07 -819.80, 198.53 -800.57, 155.42 -814.72, 133.87 -836.52, 113.31 -842.59, 92.76 -811.56, 72.20 -800.22, 22.41 -825.54, -27.38 -804.38, -77.17 -788.33, -101.51 -833.12, -150.18 -809.46, -176.02 -754.02, -201.87 -735.36, -227.71 -752.72, -255.98 -784.15, -312.52 -761.64, -455.97 -753.97, -482.15 -774.50, -508.33 -764.08, -534.51 -794.79, -633.24 -735.12, -682.61 -762.83, -747.64 -748.50, -780.16 -753.74, -807.27 -807.75, -834.38 -812.02, -861.49 -839.01, -886.97 -826.47, -912.46 -802.54, -937.94 -792.65, -963.96 -794.40, -989.99 -836.80, -1016.01 -865.82, -1044.54 -814.38, -1101.61 -799.43, -1145.74 -789.85, -1234.00 -839.87, -1323.20 -846.81, -1466.39 -835.15, -1493.61 -795.82, -1548.06 -798.22, -1579.65 -838.14, -1611.24 -846.86, -1642.84 -826.58, -1682.81 -833.75, -1702.80 -876.34, -1745.30 -826.28, -1787.80 -797.10, -1830.31 -838.59, -1864.69 -826.21, -1899.07 -836.52, -1933.45 -850.02, -1967.81 -833.71, -2002.16 -830.81, -2036.52 -817.78, -2179.27 -872.38, -2211.30 -848.86, -2243.33 -813.50, -2275.37 -792.21, -2354.46 -840.91, -2446.98 -848.56, -2549.44 -857.64, -2583.14 -799.03, -2599.98 -822.33, -2656.08 -804.45, -2684.13 -803.48, -2730.62 -762.09, -2823.60 -802.91, -2873.07 -791.15, -2972.00 -753.51, -3015.65 -798.18, -3037.48 -740.96, -3132.18 -782.55, -3179.53 -795.74, -3269.71 -846.23, -3307.96 -851.51, -3327.09 -808.18, -3435.00 -818.03, -3452.47 -816.70, -3469.94 -785.60, -3487.41 -859.30, -3513.81 -811.91, -3566.60 -845.59, -3600.13 -818.88, -3667.18 -876.82, -3739.88 -869.37, -3802.21 -857.56, -3833.37 -865.98, -3871.50 -847.56, -3909.62 -834.17, -3947.74 -888.38, -4029.09 -840.93, -4069.77 -876.66, -4211.44 -873.01, -4245.48 -907.86, -4313.58 -849.64, -4367.11 -854.26, -4497.61 -857.86, -4548.93 -824.15, -4570.89 -849.28, -4592.85 -844.81, -4614.81 -809.40, -4657.94 -840.37, -4679.50 -796.01, -4706.43 -770.24, -4760.30 -763.38, -4790.60 -765.38, -4820.91 -786.29, -4851.22 -812.62, -4909.90 -809.92, -4939.25 -782.50, -5017.37 -833.96, -5056.44 -774.00, -5097.70 -794.72, -5138.97 -794.53, -5180.24 -781.28, -5222.72 -775.99, -5265.21 -760.81, -5307.69 -800.21, -5354.93 -779.69, -5449.41 -816.43, -5536.98 -797.12, -5556.72 -814.55, -5596.19 -771.34, -5674.91 -800.51, -5726.83 -791.98, -5752.78 -780.17, -5813.72 -802.71, -5842.02 -844.45, -5870.32 -804.66, -5898.62 -824.54, -5945.47 -795.92, -6039.17 -824.19, -6069.21 -756.80, -6129.30 -813.46, -6148.46 -782.03, -6186.78 -785.93, -6243.32 -811.11, -6271.59 -802.61, -6414.47 -814.80, -6454.50 -822.34, -6494.53 -811.47, -6534.55 -788.09, -6583.29 -801.45, -6632.02 -791.97, -6680.76 -770.62, -6778.81 -779.10, -6804.14 -805.98, -6854.80 -791.93, -6872.97 -821.03, -6891.13 -792.40, -6909.30 -789.16, -6984.62 -779.37, -7022.28 -779.93, -7061.67 -752.52, -7101.06 -791.04, -7140.45 -778.51, -7274.11 -801.59, -7317.34 -813.76, -7403.80 -863.68, -7432.38 -868.56, -7460.96 -860.14, -7489.54 -861.37, -7540.43 -825.04, -7565.88 -825.50, -7659.09 -882.09, -7746.91 -783.51, -7790.82 -858.50, -7915.95 -851.57, -7941.66 -808.19, -7967.36 -812.54, -7993.07 -821.49, -8023.17 -779.84, -8053.27 -798.59, -8083.37 -802.94, -8222.92 -770.52, -8278.55 -779.20, -8347.83 -769.85, -8382.46 -698.06, -8408.41 -723.02, -8460.29 -686.72, -8608.25 -725.70, -8652.64 -701.95, -8741.42 -696.38, -8832.46 -759.67, -8873.45 -745.16, -8955.44 -688.37, -9003.73 -729.93, -9052.03 -750.21, -9100.32 -743.66, -9154.68 -763.56, -9192.31 -710.01, -9267.57 -741.56, -9312.16 -694.26, -9401.35 -734.38, -9450.09 -743.60, -9498.83 -678.55, -9547.58 -697.63, -9593.79 -698.16, -9640.00 -744.36, -9686.21 -758.13, -9728.17 -752.88, -9770.12 -734.86, -9812.07 -731.35, -9942.05 -755.60, -9962.12 -740.50, -10002.26 -680.87, -10038.16 -674.08, -10109.95 -693.81, -10168.90 -676.94, -10198.37 -768.10, -10225.53 -720.65, -10252.69 -744.01, -10279.85 -706.24, -10351.27 -727.20, -10370.71 -699.92, -10409.61 -731.22, -10466.08 -725.15, -10494.32 -758.90, -10584.77 -751.18, -10634.10 -731.61, -10683.43 -711.21, -10732.76 -768.32, -10797.10 -763.17, -10829.27 -791.05, -10873.18 -782.24, -10961.01 -819.48, -11100.81 -775.06, -11182.35 -791.80, -11163.62 -630.21))

    op_st = ['Intersects', 'Touches', 'Disjoint', 'Contains', 'Within']

    print('MR X MP -> P : N Tests: ' + str(NTESTS))
    print('Op;mET (sec);MET (sec);mSET (sec);MSET (sec);AVGET %;NV')

    k = 0
    while k < len(op_st):
        for el in tests:
            str = op_st[k] + ';'
            for e in el[k]:
                str += e + ';'

            print(str)

        k += 1

    sys.exit()

# 1. get input

begin_exec_time = time.time()
#get_params()

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
