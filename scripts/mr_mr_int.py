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

import functools

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

import math
from math import sqrt

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
    Overlaps = 7
    CoveredBy = 8
    Covers = 9

"""
class STOperation(enum.Enum): 
    Intersection = 9
"""

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
            if self.intervals[idx].contains(t):
                break

            idx += 1

        if idx >= n:
            print("ERR: Invalid instant?", idx, n, t, self.intervals[0].to_string())
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

class MovingSegment:

    def __init__(self):
        self.units = []

    def add_unit(self, unit):
        self.units += [unit]

    def at(self, t):
        """
        n = len(self.units)
        i, t = self.get_unit_and_time(t)

        if i < 0 or i > n - 1:
            return None, None, None, None

        return self.units[i].at(t)
        """

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

        """
        n = len(self.units)
        i, t = self.get_unit_and_time(t)

        if i < 0 or i > n - 1:
            return None

        return self.units[i].wkt_at(t)
        """

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

        """
        n = len(self.units)
        i, t = self.get_unit_and_time(t)
        
        if i < 0 or i > n - 1:
            return None, None, None, None

        Ax, Ay, Bx, By = self.units[int(i)].at(t)

        if (min(Ax, Bx) <= Px and Px <= max(Ax, Bx)) and (min(Ay, By) <= Py and Py <= max(Ay, By)):
            return True

        return False
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

class MovingPoint:

    def __init__(self):
        self.units = []

    def add_unit(self, unit):
        self.units += [unit]

    def get_units(self):
        return self.units

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

            idx += 1

        return None, None

        """
        idx = 0
        n = len(self.units)

        while idx < n:
            if self.units[idx].i.contains(t):
                dt = self.units[idx].i.y - self.units[idx].i.x
                t = (t - self.units[idx].i.x) / dt
                return self.units[idx].at(t)

            idx += 1

        return None, None
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

            idx += 1

        return 'LINESTRING EMPTY'

        """
        idx = 0
        n = len(self.units)

        while idx < n:
            if self.units[idx].i.contains(t):
                dt = self.units[idx].i.y - self.units[idx].i.x
                t = (t - self.units[idx].i.x) / dt
                return self.units[idx].wkt_at(t)

            idx += 1

        return 'LINESTRING EMPTY'
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

class MovingRegion:

    def __init__(self):
        self.units = []

    def add_unit(self, unit):
        self.units += [unit]

    def get_units(self):
        return self.units

    def at(self, t):
        idx = 0
        n = len(self.units)

        while idx < n:
            if self.units[idx].i.contains(t):
                return self.units[idx].at(t)

            idx += 1

        return Polygon()

    def to_string(self):
        s = "MR: ["
        idx = 0
        n = len(self.units)

        while idx < n:
            if idx > 0:
                s += ", "

            s += self.units[idx].to_string()
            idx += 1

        s += "]"
        return s

class MRU:

    #def __init__(self, p, q, ms, i):
    def __init__(self, i):
        self.p = []
        self.q = []
        self.ms = []
        self.i = i

    def add_p(self, p):
        self.p += [p]

    def add_q(self, q):
        self.q += [q]

    def add_ms(self, ms):
        self.ms += [ms]

    def at(self, t):
        region = None

        if not self.i.contains(t):
            return None

        if len(self.ms) == 1:
            if t == self.i.begin():
                return self.p[0]
            elif t == self.i.end():
                return self.q[0]
            else:
                coords = []
                ms = self.ms[0]

                x0, y0, x1, y1 = ms[0].at(t)

                coords += [[x0, y0]]
                coords += [[x1, y1]]

                k = 1
                n = len(ms)

                while k < n:
                    x0, y0, x1, y1 = ms[k].at(t)

                    coords += [[x1, y1]]
                    k += 1

                #print(coords, self.i.to_string(), t)
                return Polygon(coords)
        elif len(self.ms) == 0:
            return Polygon()
        else:
            obs = []
            if t == self.i.begin():
                for p in self.p:
                    obs += [p]
            elif t == self.i.end():
                for q in self.q:
                    obs += [q]
            else:
                for ms in self.ms:
                    if len(ms) == 0:
                        continue

                    coords = []
                    k = 0

                    x0, y0, x1, y1 = ms[k].at(t)

                    coords += [[x0, y0]]
                    coords += [[x1, y1]]

                    k = 1
                    n = len(ms)

                    while k < n:
                        x0, y0, x1, y1 = ms[k].at(t)
                        coords += [[x1, y1]]
                        k += 1

                    obs += [Polygon(coords)]

            #print(obs)
            return GeometryCollection(obs)

    #def to_string(self):
    #    return "MSU: c0: " + self.c0.to_string() + ", c1: " + self.c1.to_string() + ", i: " + self.i.to_string()

class Values:

    def __init__(self, u, v):
        self.u = u
        self.v = v

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
precision_0 = '.0f'
#tprecision = '.3f'
operation = 1
eps = 0.000001				# Temporal eps.
err_msg = None
err_code = 0
initial_state = None
final_state = None
#tepsilon = 0.0000001			# Spatial eps.

#DEBUG = False
DEBUG = True
TESTING = 0
#NTESTS = 1

#print(Operation.Intersects.value)

"""
if Operation.Intersects.value == operation:
    print('Op: Intersects')
"""

"""
point = shPoint(0.5, 0.5)
polygon = shPolygon([(0, 0), (0, 1), (1, 1), (1, 0)])
print(polygon.contains(point))
"""

def distance(x1, y1, x2, y2):
    return sqrt((x2 - x1)**2 + (y2 - y1)**2)

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
"""
def get_params():
    global pass_through_control_points
    global print_intersection_information
    global print_solver_execution_time
    global n_samples
    global interval
    global epsilon
    global precision
    global operation

    if sys.argv[3] == "0":
        pass_through_control_points = False
    
    if sys.argv[4] == "0":
        print_intersection_information = False

    if sys.argv[5] == "1":
        print_solver_execution_time = True

    n_samples = int(sys.argv[6])

    v = sys.argv[7].split(',')

    if len(v) != 2:
        print('ERR: Invalid interval data!')
        sys.exit()

    interval.x = float(v[0])
    interval.y = float(v[1])
	
    epsilon = float(sys.argv[8])
    precision = '.' + sys.argv[9] + 'f'
    operation = int(sys.argv[10])
"""

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
    #global NTESTS

    """
    if len(sys.argv) == 2:
        TESTING = True
        NTESTS = int(sys.argv[1])
        return
    """

    if sys.argv[5] == "0":
        pass_through_control_points = False
    
    if sys.argv[6] == "0":
        print_intersection_information = False

    if sys.argv[7] == "1":
        print_solver_execution_time = True

    n_samples = int(sys.argv[8])

    v = sys.argv[9].split(',')

    if len(v) != 2:
        err_msg = 'get_params : Invalid interval data!'
        return

    interval.x = float(v[0])
    interval.y = float(v[1])
	
    epsilon = float(sys.argv[10])
    precision = '.' + sys.argv[11] + 'f'
    operation = int(sys.argv[12])

    if len(sys.argv) > 13:
        TESTING = int(sys.argv[13])
        #if int(sys.argv[13]) == 1:
        #    TESTING = True

        #NTESTS = int(sys.argv[13])
        #return

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

def create_moving_segment_and_mp(units, pass_through_control_points, t0, t1, p, q, MS, FIND_INT_FUNC = False):
    ms = MovingSegment()
    mp_units = []

    for u in units:
        c0 = CCurve()
        c1 = CCurve()

        u = u.split("#")
        t = 0.5

        if len(u) != 3:
            print_error(-1, 'create_moving_segment > Invalid unit data! ' + u)

        cp0 = u[0].split(",")
        cp1 = u[1].split(",")
        intervals = u[2].split(":")

        if len(cp0) != len(cp1):
            print_error(-1, 'create_moving_segment > Different number of control points! ' + cp0 + ' : ' + cp1)

        if (len(cp0) - 6) % 2 != 0 or (len(cp1) - 6) % 2 != 0:
            print_error(-1, 'create_moving_segment > Invalid control points data! ' + cp0 + ' : ' + cp1)

        m = ((len(cp0) - 6) / 4) + 1

        if (len(intervals)) - 1 != m:
            print_error(-1, 'create_moving_segment > Invalid interval data! ' + str(len(intervals) - 1) + ' : ' + str(m))

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
                unit = [p0.x, p0.y, x, y, p2.x, p2.y]
            else:
                c = QuadBezierCurve(p0, p1, p2)
                unit = [p0.x, p0.y, p1.x, p1.y, p2.x, p2.y]

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

        unit = [[unit, i.begin(), i.end()], [i.begin(), i.end()]]
        mp_units += [unit]

    mpoint = create_moving_point10(mp_units)

    x, y = mpoint.at(t0)
    ipoint = shapely.geometry.Point(x, y)

    x, y = mpoint.at(t1)
    fpoint = shapely.geometry.Point(x, y)

    mp_i_state, mp_f_state = get_states_mp_mr(p, q, ipoint, fpoint)
    it = get_mr_mp_intersections2(MS, mpoint, mp_i_state, mp_f_state, 1, True)

    begin_exec_time = time.time()
    G = None
    if FIND_INT_FUNC:
        G = get_F(MS, ms, i)
    end_exec_time = time.time()

    return ms, mpoint, it, G, (end_exec_time - begin_exec_time)

def create_moving_segment2(units, pass_through_control_points, _units = None):
    ms = MovingSegment()

    if _units != None:
        for u in _units:
            c0 = CCurve()
            c1 = CCurve()

            t = 0.5

            N = len(u) - 1
            i = Interval(u[N][0], u[N][1], True, False)

            K = 0
            while K < N:
                cp0 = u[K][0]
                cp1 = u[K][1]

                ui = Interval(u[K][2], u[K][3], True, False)

                p0 = Point(cp0[0], cp0[1])
                p1 = Point(cp0[2], cp0[3])
                p2 = Point(cp0[4], cp0[5])

                if pass_through_control_points:
                    x = 2 * p1.x - t * p0.x - t * p2.x
                    y = 2 * p1.y - t * p0.y - t * p2.y
                    c = QuadBezierCurve(p0, Point(x, y), p2)
                else:
                    c = QuadBezierCurve(p0, p1, p2)

                c0.add_curve(c, ui)

                p0 = Point(cp1[0], cp1[1])
                p1 = Point(cp1[2], cp1[3])
                p2 = Point(cp1[4], cp1[5])

                if pass_through_control_points:
                    x = 2 * p1.x - t * p0.x - t * p2.x
                    y = 2 * p1.y - t * p0.y - t * p2.y

                    c = QuadBezierCurve(p0, Point(x, y), p2)
                else:
                    c = QuadBezierCurve(p0, p1, p2)

                c1.add_curve(c, ui)

                K += 1

            u = MSU(c0, c1, i)
            ms.add_unit(u)

        return ms

    for u in units:
        c0 = CCurve()
        c1 = CCurve()

        u = u.split("#")
        t = 0.5

        if len(u) != 3:
            print_error(-1, 'create_moving_segment > Invalid unit data! ' + u)

        cp0 = u[0].split(",")
        cp1 = u[1].split(",")
        intervals = u[2].split(":")

        if len(cp0) != len(cp1):
            print_error(-1, 'create_moving_segment > Different number of control points! ' + cp0 + ' : ' + cp1)

        if (len(cp0) - 6) % 2 != 0 or (len(cp1) - 6) % 2 != 0:
            print_error(-1, 'create_moving_segment > Invalid control points data! ' + cp0 + ' : ' + cp1)

        m = ((len(cp0) - 6) / 4) + 1

        if (len(intervals)) - 1 != m:
            print_error(-1, 'create_moving_segment > Invalid interval data! ' + str(len(intervals) - 1) + ' : ' + str(m))

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
# Create a moving point.
#-------------------------------------------------------------------
def create_moving_point(units):
    mp = MovingPoint()

    for u in units:
        u = u.split("#")

        if len(u) != 3:
            print(u)
            print("ERR: Invalid unit data.")
            sys.exit()

        cp0 = u[0].split(",")
        cp1 = u[1].split(",")
        intervals = u[2].split(":")

        if len(cp0) != len(cp1) or len(cp0) != 2:
            print(cp0)
            print(cp1)
            print("ERR: Different number of control points.")
            sys.exit()

        if len(intervals) != 1:
            print(len(intervals))
            print("ERR: Invalid interval data.")
            sys.exit()

        i = intervals[0].split(",")
        i = Interval(float(i[0]), float(i[1]), True, False)

        p0 = Point(float(cp0[0]), float(cp0[1]))
        p1 = Point(float(cp1[0]), float(cp1[1]))

        msu = MPU([p0, p1], i)
        mp.add_unit(msu)

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

    return GeometryCollection(lines)
    #return MultiLineString(lines)

def get_mseg_coords(ms, t):
    return ms.at(t)

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

def get_vertex_at(msegs, t):
    x0, y0, x1, y1 = msegs[0].at(t)
    return shapely.geometry.Point(x0, y0)

def get_lines(MS, t):
    for ms in MS:
        print(ms.obj_at(t).wkt + ';')

def get_samples_for_out(MS0, MS1, i, n_samples, s):
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

        mline0 = get_mline(MS0, t)
        mline1 = get_mline(MS1, t)

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    """
                    if J < N and t >= T[J]:
                        t = T[J]
                        J += 1

                    mline = get_mline(MS, t)
                    """
                    print(mline0.wkt)
                    print(mline1.wkt)

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
                    print(mline0.wkt)
                    print(mline1.wkt)

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
            print(mline0.wkt)
            print(mline1.wkt)
            print(out)
        else:
            eq = False

def get_samples_for_out2(MS0, MS1, i, n_samples, s, x1, y1, x2, y2, dx1, dx2, dy1, dy2):
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
        t01 = (t - i.x) / dt
        out = 0
        flag = False

        if J < N and t >= T[J]:
            t = T[J]
            t01 = (t - i.x) / dt
            out = K[J]
            J += 1
            flag = True

        mline0 = get_mline(MS0, t)
        mline1 = get_mline(MS1, t)

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    print(mline0.wkt)
                    print(mline1.wkt)

                    if flag:
                        if out == 1:
                            _x1, _y1, _x2, _y2 = get_mseg_coords(MS1[0], t)
                            x = get_x(t01)
                            y = get_y(x1, y1, x2, y2, dx1, dx2, dy1, dy2, t01, x)
                            l = LineString([(_x2, _y2), (x, y)])
                            print(l)
                        else:
                            print('LINESTRING EMPTY')
                        print(out)
                    else:
                        _x1, _y1, _x2, _y2 = get_mseg_coords(MS1[0], t)
                        x = get_x(t01)
                        y = get_y(x1, y1, x2, y2, dx1, dx2, dy1, dy2, t01, x)
                        l = LineString([(_x2, _y2), (x, y)])
                        print(l)
                        print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    print(mline0.wkt)
                    print(mline1.wkt)

                    if flag:
                        if out == 1:
                            _x1, _y1, _x2, _y2 = get_mseg_coords(MS1[0], t)
                            x = get_x(t01)
                            y = get_y(x1, y1, x2, y2, dx1, dx2, dy1, dy2, t01, x)
                            l = LineString([(_x2, _y2), (x, y)])
                            print(l)
                        else:
                            print('LINESTRING EMPTY')
                        print(out)
                    else:
                        _x1, _y1, _x2, _y2 = get_mseg_coords(MS1[0], t)
                        x = get_x(t01)
                        y = get_y(x1, y1, x2, y2, dx1, dx2, dy1, dy2, t01, x)
                        l = LineString([(_x2, _y2), (x, y)])
                        print(l)
                        print(1)

                    k += 1

                    eq = True

        if not eq:
            print(mline0.wkt)
            print(mline1.wkt)

            if out == 1:
                _x1, _y1, _x2, _y2 = get_mseg_coords(MS1[0], t)
                x = get_x(t01)
                y = get_y(x1, y1, x2, y2, dx1, dx2, dy1, dy2, t01, x)
                l = LineString([(_x2, _y2), (x, y)])
                print(l)
            else:
                print('LINESTRING EMPTY')
            print(out)
        else:
            eq = False

def get_samples_for_out3(MS0, MS1, i, n_samples, s, ms):
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
        t01 = (t - i.x) / dt
        out = 0
        flag = False

        if J < N and t >= T[J]:
            t = T[J]
            t01 = (t - i.x) / dt
            out = K[J]
            J += 1
            flag = True

        mline0 = get_mline(MS0, t)
        mline1 = get_mline(MS1, t)

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    print(mline0.wkt)
                    print(mline1.wkt)

                    if flag:
                        if out == 1:
                            _x1, _y1, _x2, _y2 = get_mseg_coords(MS1[0], t)
                            x = get_xx(t)
                            y = get_yy(ms, t, x)
                            l = LineString([(_x2, _y2), (x, y)])
                            print(l)
                        else:
                            print('LINESTRING EMPTY')
                        print(out)
                    else:
                        _x1, _y1, _x2, _y2 = get_mseg_coords(MS1[0], t)
                        x = get_xx(t)
                        y = get_yy(ms, t, x)
                        l = LineString([(_x2, _y2), (x, y)])
                        print(l)
                        print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    print(mline0.wkt)
                    print(mline1.wkt)

                    if flag:
                        if out == 1:
                            _x1, _y1, _x2, _y2 = get_mseg_coords(MS1[0], t)
                            x = get_xx(t)
                            y = get_yy(ms, t, x)
                            l = LineString([(_x2, _y2), (x, y)])
                            print(l)
                        else:
                            print('LINESTRING EMPTY')
                        print(out)
                    else:
                        _x1, _y1, _x2, _y2 = get_mseg_coords(MS1[0], t)
                        x = get_xx(t)
                        y = get_yy(ms, t, x)
                        l = LineString([(_x2, _y2), (x, y)])
                        print(l)
                        print(1)

                    k += 1

                    eq = True

        if not eq:
            print(mline0.wkt)
            print(mline1.wkt)

            if out == 1:
                _x1, _y1, _x2, _y2 = get_mseg_coords(MS1[0], t)
                x = get_xx(t)
                y = get_yy(ms, t, x)
                l = LineString([(_x2, _y2), (x, y)])
                print(l)
            else:
                print('LINESTRING EMPTY')
            print(out)
        else:
            eq = False

def my_2d_sort(p1, p2):
    if p1.x < p2.x:
        return -1
    elif p1.x > p2.x:
        return 1

    if p1.y < p2.y:
        return -1
    elif p1.y > p2.y:
        return 1

    return 0

def get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2, idx = 1):
    u = 0
    M = len(II)
    coll = []

    mpoint1_in = False
    mpoint2_in = False

    mpoint1_pos = None
    mpoint2_pos = None

    while u < M:
        IT = II[u]

        for it in IT:
            if isinstance(it, Interval) and it.contains(t):
                f = None

                if idx == 1:
                    f = globals()["get_x%s" % u]
                elif idx == 2:
                    f = globals()["get_xx%s" % u]
                elif idx == 3:
                    f = globals()["get_xxx%s" % u]

                x = f(t)
                y = get_yy(MSEG[u][1], t, x)

                coll += [shapely.geometry.Point(x, y)]
        u += 1

    if i1_idx < i1_len:
        _it = i1[i1_idx]
        
        if _it.contains(t):
            x, y = mpoint1.at(t)
            mpoint1_pos = shapely.geometry.Point(x, y)
            mpoint1_in = True
            coll += [mpoint1_pos]

    if i2_idx < i2_len:
        _it = i2[i2_idx]
        
        if _it.contains(t):
            x, y = mpoint2.at(t)
            mpoint2_pos = shapely.geometry.Point(x, y)
            mpoint2_in = True
            coll += [mpoint2_pos]

    coll = sorted(coll, key=functools.cmp_to_key(my_2d_sort))

    # the segment is inside the region
    if  mpoint1_in and mpoint2_in and len(coll) == 2:
        l = LineString([(coll[0].x, coll[0].y), (coll[1].x, coll[1].y)])
        return [l]
        #print(GeometryCollection([l]).wkt)
    elif len(coll) == 1:
        #print(GeometryCollection(coll).wkt)
        return coll
    else:
        p1_on = False
        p2_on = False

        _out = []
        IDX = 0

        if mpoint1_in and coll[0].x == mpoint1_pos.x and coll[0].y == mpoint1_pos.y:
            for it in i1:
                if isinstance(it, Interval):
                    if t == it.x or t == it.y:
                        p1_on = True
                        break
                elif t == it:
                    p1_on = True
        elif mpoint2_in and coll[0].x == mpoint2_pos.x and coll[0].y == mpoint2_pos.y:
            for it in i2:
                if isinstance(it, Interval):
                    if t == it.x or t == it.y:
                        p2_on = True
                        break
                elif t == it:
                    p2_on = True

        if p1_on:
            _out += [mpoint1_pos]
            IDX = 1
        elif p2_on:
            _out += [mpoint2_pos]
            IDX = 1

        LEN = len(coll)
        #IDX = 0
        check = False
        while IDX < LEN - 1:
            curr = coll[IDX]
            next = coll[IDX+1]
            l = LineString([(curr.x, curr.y), (next.x, next.y)])
            _out += [l]
            IDX += 2

            if IDX == LEN - 1:
                check = True
                break

        if check:
            p = coll[IDX]

            if mpoint1_in and p.x == mpoint1_pos.x and p.y == mpoint1_pos.y:
                _out += [mpoint1_pos]
            elif mpoint2_in and p.x == mpoint2_pos.x and p.y == mpoint2_pos.y:
                _out += [mpoint2_pos]
            elif mpoint1_in:
                l = LineString([(mpoint1_pos.x, mpoint1_pos.y), (p.x, p.y)])
                _out += [l]
            elif mpoint2_in:
                l = LineString([(mpoint2_pos.x, mpoint2_pos.y), (p.x, p.y)])
                _out += [l]

        #print(GeometryCollection(_out).wkt)
        return _out

def get_seg2(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2, idx = 1):
    u = 0
    M = len(II)
    coll = []

    mpoint1_in = False
    mpoint2_in = False

    mpoint1_pos = None
    mpoint2_pos = None

    while u < M:
        IT = II[u]

        for it in IT:
            if isinstance(it, Interval) and it.contains(t):
                f = None

                if idx == 1:
                    f = globals()["get_x%s" % u]
                elif idx == 2:
                    f = globals()["get_xx%s" % u]
                elif idx == 3:
                    f = globals()["get_xxx%s" % u]

                x = f(t)
                y = get_yy(MSEG[u][1], t, x)

                coll += [shapely.geometry.Point(x, y)]
        u += 1

    if i1_idx < i1_len:
        _it = i1[i1_idx]
        
        if _it.contains(t):
            x, y = mpoint1.at(t)
            mpoint1_pos = shapely.geometry.Point(x, y)
            mpoint1_in = True
            coll += [mpoint1_pos]

    if i2_idx < i2_len:
        _it = i2[i2_idx]
        
        if _it.contains(t):
            x, y = mpoint2.at(t)
            mpoint2_pos = shapely.geometry.Point(x, y)
            mpoint2_in = True
            coll += [mpoint2_pos]

    coll = sorted(coll, key=functools.cmp_to_key(my_2d_sort))

    # the segment is inside the region
    if  mpoint1_in and mpoint2_in and len(coll) == 2:
        l = LineString([(coll[0].x, coll[0].y), (coll[1].x, coll[1].y)])
        return [l]
        #print(GeometryCollection([l]).wkt)
    elif len(coll) == 1:
        #print(GeometryCollection(coll).wkt)
        return coll
    else:
        p1_on = False
        p2_on = False

        _out = []
        IDX = 0

        if mpoint1_in and coll[0].x == mpoint1_pos.x and coll[0].y == mpoint1_pos.y:
            for it in i1:
                if isinstance(it, Interval):
                    if t == it.x or t == it.y:
                        p1_on = True
                        break
                elif t == it:
                    p1_on = True
        elif mpoint2_in and coll[0].x == mpoint2_pos.x and coll[0].y == mpoint2_pos.y:
            for it in i2:
                if isinstance(it, Interval):
                    if t == it.x or t == it.y:
                        p2_on = True
                        break
                elif t == it:
                    p2_on = True

        if p1_on:
            _out += [mpoint1_pos]
            IDX = 1
        elif p2_on:
            _out += [mpoint2_pos]
            IDX = 1

        LEN = len(coll)
        #IDX = 0
        check = False
        while IDX < LEN - 1:
            curr = coll[IDX]
            next = coll[IDX+1]
            l = LineString([(curr.x, curr.y), (next.x, next.y)])
            _out += [l]
            IDX += 2

            if IDX == LEN - 1:
                check = True
                break

        if check:
            p = coll[IDX]

            if mpoint1_in and p.x == mpoint1_pos.x and p.y == mpoint1_pos.y:
                _out += [mpoint1_pos]
            elif mpoint2_in and p.x == mpoint2_pos.x and p.y == mpoint2_pos.y:
                _out += [mpoint2_pos]
            elif mpoint1_in:
                l = LineString([(mpoint1_pos.x, mpoint1_pos.y), (p.x, p.y)])
                _out += [l]
            elif mpoint2_in:
                l = LineString([(mpoint2_pos.x, mpoint2_pos.y), (p.x, p.y)])
                _out += [l]

        #print(GeometryCollection(_out).wkt)
        return _out

#def get_samples_for_out4(MS0, MS1, i, n_samples, s, ms):
def get_samples_for_out4(MS, G, MSEG, II, ms, i, n_samples, s, i1, i2, mpoint1, mpoint2):
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
    i1_len = len(i1)
    i2_len = len(i2)
    i1_idx = 0
    i2_idx = 0

    for j in range(0, n_samples):
        t = i.x + dt * (float(j) / n)
        t01 = (t - i.x) / dt
        out = 0
        flag = False

        mpoint1_in = False
        mpoint2_in = False

        mpoint1_pos = None
        mpoint2_pos = None

        if J < N and t >= T[J]:
            t = T[J]
            t01 = (t - i.x) / dt
            out = K[J]
            J += 1
            flag = True

        #mline0 = get_mline(MS0, t)
        #mline1 = get_mline(MS1, t)
        mline0 = get_region_at(MS, t)
        mline1 = ms.obj_at(t)

        #GeometryCollection(lines)
        coll = []

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    print(mline0.wkt)
                    print(mline1.wkt)

                    if flag:
                        if out == 1:
                            get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                            """
                            u = 0
                            M = len(II)
                            while u < M:
                                IT = II[u]

                                for it in IT:
                                    if isinstance(it, Interval) and it.contains(t):
                                        #print(u, t, it.to_string())
                                        f = globals()["get_xx%s" % u]

                                        x = f(t)
                                        #print(MSEG[u][1], t, x)
                                        y = get_yy(MSEG[u][1], t, x)

                                        coll += [shapely.geometry.Point(x, y)]
                                u += 1

                            if i1_idx < i1_len:
                                _it = i1[i1_idx]
                                
                                if _it.contains(t):
                                    x, y = mpoint1.at(t)
                                    mpoint1_pos = shapely.geometry.Point(x, y)
                                    mpoint1_in = True
                                    coll += [mpoint1_pos]

                            if i2_idx < i2_len:
                                _it = i2[i2_idx]
                                
                                if _it.contains(t):
                                    x, y = mpoint2.at(t)
                                    mpoint2_pos = shapely.geometry.Point(x, y)
                                    mpoint2_in = True
                                    coll += [mpoint2_pos]

                            coll = sorted(coll, key=functools.cmp_to_key(my_2d_sort))

                            # the segment is inside the region
                            if  mpoint1_in and mpoint2_in and len(coll) == 2:
                                l = LineString([(coll[0].x, coll[0].y), (coll[1].x, coll[1].y)])
                                print(GeometryCollection([l]).wkt)
                            elif len(coll) == 1:
                                print(GeometryCollection(coll).wkt)
                            else:
                                p1_on = False
                                p2_on = False

                                _out = []
                                IDX = 0

                                if mpoint1_in and coll[0].x == mpoint1_pos.x and coll[0].y == mpoint1_pos.y:
                                    for it in i1:
                                        if isinstance(it, Interval):
                                            if t == it.x or t == it.y:
                                                p1_on = True
                                                break
                                        elif t == it:
                                            p1_on = True
                                elif mpoint2_in and coll[0].x == mpoint2_pos.x and coll[0].y == mpoint2_pos.y:
                                    for it in i2:
                                        if isinstance(it, Interval):
                                            if t == it.x or t == it.y:
                                                p2_on = True
                                                break
                                        elif t == it:
                                            p2_on = True

                                if p1_on:
                                    _out += [mpoint1_pos]
                                    IDX = 1
                                elif p2_on:
                                    _out += [mpoint2_pos]
                                    IDX = 1

                                LEN = len(coll)
                                #IDX = 0
                                check = False
                                while IDX < LEN - 1:
                                    curr = coll[IDX]
                                    next = coll[IDX+1]
                                    l = LineString([(curr.x, curr.y), (next.x, next.y)])
                                    _out += [l]
                                    IDX += 2

                                    if IDX == LEN - 1:
                                        check = True
                                        break

                                if check:
                                    p = coll[IDX]

                                    if mpoint1_in and p.x == mpoint1_pos.x and p.y == mpoint1_pos.y:
                                        _out += [mpoint1_pos]
                                    elif mpoint2_in and p.x == mpoint2_pos.x and p.y == mpoint2_pos.y:
                                        _out += [mpoint2_pos]
                                    elif mpoint1_in:
                                        l = LineString([(mpoint1_pos.x, mpoint1_pos.y), (p.x, p.y)])
                                        _out += [l]
                                    elif mpoint2_in:
                                        l = LineString([(mpoint2_pos.x, mpoint2_pos.y), (p.x, p.y)])
                                        _out += [l]

                                print(GeometryCollection(_out).wkt)
                            """
                        else:
                            print('LINESTRING EMPTY')
                        print(out)
                    else:
                        """
                        u = 0
                        M = len(II)
                        while u < M:
                            IT = II[u]

                            for it in IT:
                                if isinstance(it, Interval) and it.contains(t):
                                    #print(u, t, it.to_string())
                                    f = globals()["get_xx%s" % u]

                                    x = f(t)
                                    y = get_yy(MSEG[u][1], t, x)

                                    coll += [shapely.geometry.Point(x, y)]
                            u += 1

                        if i1_idx < i1_len:
                            _it = i1[i1_idx]
                                
                            if _it.contains(t):
                                mpoint1_in = True
                                x, y = mpoint1.at(t)

                                coll += [shapely.geometry.Point(x, y)]

                        if i2_idx < i2_len:
                            _it = i2[i2_idx]
                                
                            if _it.contains(t):
                                mpoint2_in = True
                                x, y = mpoint2.at(t)
                                coll += [shapely.geometry.Point(x, y)]

                        print(GeometryCollection(coll).wkt)
                        """

                        """
                        u = 0
                        M = len(II)
                        while u < M:
                            IT = II[u]

                            for it in IT:
                                if isinstance(it, Interval) and it.contains(t):
                                    f = globals()["get_xx%s" % u]

                                    x = f(t)
                                    y = get_yy(MSEG[u][1], t, x)

                                    coll += [shapely.geometry.Point(x, y)]
                            u += 1

                        if i1_idx < i1_len:
                            _it = i1[i1_idx]
                                
                            if _it.contains(t):
                                x, y = mpoint1.at(t)
                                mpoint1_pos = shapely.geometry.Point(x, y)
                                mpoint1_in = True
                                coll += [mpoint1_pos]

                        if i2_idx < i2_len:
                            _it = i2[i2_idx]
                                
                            if _it.contains(t):
                                x, y = mpoint2.at(t)
                                mpoint2_pos = shapely.geometry.Point(x, y)
                                mpoint2_in = True
                                coll += [mpoint2_pos]

                        coll = sorted(coll, key=functools.cmp_to_key(my_2d_sort))

                        # the segment is inside the region
                        if  mpoint1_in and mpoint2_in and len(coll) == 2:
                            l = LineString([(coll[0].x, coll[0].y), (coll[1].x, coll[1].y)])
                            print(GeometryCollection([l]).wkt)
                        elif len(coll) == 1:
                            print(GeometryCollection(coll).wkt)
                        else:
                            p1_on = False
                            p2_on = False

                            _out = []
                            IDX = 0

                            if mpoint1_in and coll[0].x == mpoint1_pos.x and coll[0].y == mpoint1_pos.y:
                                for it in i1:
                                    if isinstance(it, Interval):
                                        if t == it.x or t == it.y:
                                            p1_on = True
                                            break
                                    elif t == it:
                                        p1_on = True
                            elif mpoint2_in and coll[0].x == mpoint2_pos.x and coll[0].y == mpoint2_pos.y:
                                for it in i2:
                                    if isinstance(it, Interval):
                                        if t == it.x or t == it.y:
                                            p2_on = True
                                            break
                                    elif t == it:
                                        p2_on = True

                            if p1_on:
                                _out += [mpoint1_pos]
                                IDX = 1
                            elif p2_on:
                                _out += [mpoint2_pos]
                                IDX = 1

                            LEN = len(coll)

                            check = False
                            while IDX < LEN - 1:
                                curr = coll[IDX]
                                next = coll[IDX+1]
                                l = LineString([(curr.x, curr.y), (next.x, next.y)])
                                _out += [l]
                                IDX += 2

                                if IDX == LEN - 1:
                                    check = True
                                    break

                            if check:
                                p = coll[IDX]

                                if mpoint1_in and p.x == mpoint1_pos.x and p.y == mpoint1_pos.y:
                                    _out += [mpoint1_pos]
                                elif mpoint2_in and p.x == mpoint2_pos.x and p.y == mpoint2_pos.y:
                                    _out += [mpoint2_pos]
                                elif mpoint1_in:
                                    l = LineString([(mpoint1_pos.x, mpoint1_pos.y), (p.x, p.y)])
                                    _out += [l]
                                elif mpoint2_in:
                                    l = LineString([(mpoint2_pos.x, mpoint2_pos.y), (p.x, p.y)])
                                    _out += [l]

                            print(GeometryCollection(_out).wkt)
                        """

                        get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                        print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    print(mline0.wkt)
                    print(mline1.wkt)

                    if flag:
                        if out == 1:
                            get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)

                            """
                            u = 0
                            M = len(II)
                            while u < M:
                                IT = II[u]

                                for it in IT:
                                    if isinstance(it, Interval) and it.contains(t):
                                        #print(u, t, it.to_string())
                                        f = globals()["get_xx%s" % u]

                                        x = f(t)
                                        y = get_yy(MSEG[u][1], t, x)

                                        coll += [shapely.geometry.Point(x, y)]
                                u += 1

                            if i1_idx < i1_len:
                                _it = i1[i1_idx]
                                
                                if _it.contains(t):
                                    x, y = mpoint1.at(t)
                                    coll += [shapely.geometry.Point(x, y)]

                            if i2_idx < i2_len:
                                _it = i2[i2_idx]
                                
                                if _it.contains(t):
                                    x, y = mpoint2.at(t)
                                    coll += [shapely.geometry.Point(x, y)]

                            print(GeometryCollection(coll).wkt)
                            """
                        else:
                            print('LINESTRING EMPTY')

                        print(out)
                    else:
                        get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)

                        """
                        u = 0
                        M = len(II)
                        while u < M:
                            IT = II[u]

                            for it in IT:
                                if isinstance(it, Interval) and it.contains(t):
                                    #print(u, t, it.to_string())
                                    f = globals()["get_xx%s" % u]

                                    x = f(t)
                                    y = get_yy(MSEG[u][1], t, x)

                                    coll += [shapely.geometry.Point(x, y)]
                            u += 1

                        if i1_idx < i1_len:
                            _it = i1[i1_idx]
                                
                            if _it.contains(t):
                                x, y = mpoint1.at(t)
                                coll += [shapely.geometry.Point(x, y)]

                        if i2_idx < i2_len:
                            _it = i2[i2_idx]
                                
                            if _it.contains(t):
                                x, y = mpoint2.at(t)
                                coll += [shapely.geometry.Point(x, y)]

                        print(GeometryCollection(coll).wkt)
                        """
                        print(1)

                    k += 1

                    eq = True

        if not eq:
            print(mline0.wkt)
            print(mline1.wkt)

            if out == 1:
                get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)

                """
                u = 0
                M = len(II)
                while u < M:
                    IT = II[u]

                    for it in IT:
                        if isinstance(it, Interval) and it.contains(t):
                            #print(u, t, it.to_string())
                            f = globals()["get_xx%s" % u]

                            x = f(t)
                            y = get_yy(MSEG[u][1], t, x)

                            coll += [shapely.geometry.Point(x, y)]
                    u += 1

                    if i1_idx < i1_len:
                        _it = i1[i1_idx]
                                
                        if _it.contains(t):
                            x, y = mpoint1.at(t)
                            coll += [shapely.geometry.Point(x, y)]

                    if i2_idx < i2_len:
                        _it = i2[i2_idx]
                                
                        if _it.contains(t):
                            x, y = mpoint2.at(t)
                            coll += [shapely.geometry.Point(x, y)]

                print(GeometryCollection(coll).wkt)
                """
            else:
                print('LINESTRING EMPTY')
            print(out)
        else:
            eq = False

def get_samples_for_out5(MS, G, G1, G2, MSEG, MSEG1, MSEG2, II, II1, II2, ms1, ms2, ms3, i, n_samples, s, i1, i2, i3, mpoint1, mpoint2, mpoint3):
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
    i1_len = len(i1)
    i2_len = len(i2)
    i3_len = len(i3)
    i1_idx = 0
    i2_idx = 0
    i3_idx = 0

    for j in range(0, n_samples):
        t = i.x + dt * (float(j) / n)
        t01 = (t - i.x) / dt
        out = 0
        flag = False

        #mpoint1_in = False
        #mpoint2_in = False

        #mpoint1_pos = None
        #mpoint2_pos = None

        if J < N and t >= T[J]:
            t = T[J]
            t01 = (t - i.x) / dt
            out = K[J]
            J += 1
            flag = True

        mline0 = get_region_at(MS, t)
        mline1 = ms1.obj_at(t)
        mline2 = ms2.obj_at(t)
        mline3 = ms3.obj_at(t)

        #print(GeometryCollection([mline1, mline2, mline3]).wkt)

        coll = []

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    print(mline0.wkt)
                    #print(mline1.wkt)
                    print(GeometryCollection([mline1, mline2, mline3]).wkt)

                    if flag:
                        if out == 1:
                            _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                            _out += get_seg(II1, MSEG1, t, i1_idx, i1_len, mpoint1, i1, i3_idx, i3_len, mpoint3, i3, 2)
                            _out += get_seg(II2, MSEG2, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 3)
                            print(GeometryCollection(_out).wkt)
                        else:
                            print('LINESTRING EMPTY')
                        print(out)
                    else:
                        _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                        _out += get_seg(II1, MSEG1, t, i1_idx, i1_len, mpoint1, i1, i3_idx, i3_len, mpoint3, i3, 2)
                        _out += get_seg(II2, MSEG2, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 3)
                        print(GeometryCollection(_out).wkt)
                        print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    print(mline0.wkt)
                    #print(mline1.wkt)
                    print(GeometryCollection([mline1, mline2, mline3]).wkt)

                    if flag:
                        if out == 1:
                            _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                            _out += get_seg(II1, MSEG1, t, i1_idx, i1_len, mpoint1, i1, i3_idx, i3_len, mpoint3, i3, 2)
                            _out += get_seg(II2, MSEG2, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 3)
                            print(GeometryCollection(_out).wkt)
                        else:
                            print('LINESTRING EMPTY')

                        print(out)
                    else:
                        _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                        _out += get_seg(II1, MSEG1, t, i1_idx, i1_len, mpoint1, i1, i3_idx, i3_len, mpoint3, i3, 2)
                        _out += get_seg(II2, MSEG2, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 3)
                        print(GeometryCollection(_out).wkt)
                        print(1)

                    k += 1

                    eq = True

        if not eq:
            print(mline0.wkt)
            #print(mline1.wkt)
            print(GeometryCollection([mline1, mline2, mline3]).wkt)

            if out == 1:
                _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                _out += get_seg(II1, MSEG1, t, i1_idx, i1_len, mpoint1, i1, i3_idx, i3_len, mpoint3, i3, 2)
                _out += get_seg(II2, MSEG2, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 3)
                print(GeometryCollection(_out).wkt)
            else:
                print('LINESTRING EMPTY')
            print(out)
        else:
            eq = False

def get_idx(m, n, M, N):
    id0 = 0
    id1 = 0
    id2 = 0
    id3 = 0

    if m == M:
        id0 = m
        id1 = 0
    else:
        id0 = m
        id1 = m + 1

    if n == N:
        id2 = n
        id3 = 0
    else:
        id2 = n
        id3 = n + 1

    return id0, id1, id2, id3

def print_period(p):
    #print('')

    if p == None or len(p) == 0:
        print('[]')

    for i in p:
        if isinstance(i, Interval):
            print(i.to_string())
        else:
            print(i)
			
    #print('')

def print_i_periods(p):
    print('')

    if p == None or len(p) == 0:
        print('[]')

    for i in p:
        print_period(i)

    print('')

#	get_samples_for_out6(MS, G, G1, G2, M, M1, M2, I, I1, I2, ms1, ms2, ms3, interval, n_samples, intersections, i1, i2, i3, mpoint1, mpoint2, mpoint3)
def get_samples_for_out6(MS, G, G1, G2, MSEG, MSEG1, MSEG2, II, II1, II2, ms1, ms2, ms3, i, n_samples, s, i1, i2, i3, mpoint1, mpoint2, mpoint3):
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
    i1_len = len(i1)
    i2_len = len(i2)
    i3_len = len(i3)
    i1_idx = 0
    i2_idx = 0
    i3_idx = 0

    LENMS = len(MS)
    LETRI = 3

    """
    print_i_periods(II)
    print_i_periods(II1)
    print_i_periods(II2)
    sys.exit()
    """

    for j in range(0, n_samples):
        t = i.x + dt * (float(j) / n)
        t01 = (t - i.x) / dt
        out = 0
        flag = False

        #mpoint1_in = False
        #mpoint2_in = False

        #mpoint1_pos = None
        #mpoint2_pos = None

        if J < N and t >= T[J]:
            t = T[J]
            t01 = (t - i.x) / dt
            out = K[J]
            J += 1
            flag = True

        mline0 = get_region_at(MS, t)
        mline1 = ms1.obj_at(t)
        mline2 = ms2.obj_at(t)
        mline3 = ms3.obj_at(t)

        #print(GeometryCollection([mline1, mline2, mline3]).wkt)

        coll = []

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    print(mline0.wkt)
                    #print(mline1.wkt)
                    print(GeometryCollection([mline1, mline2, mline3]).wkt)

                    if flag:
                        if out == 1:
                            _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                            _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                            _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)

                            """
                            if len(_out) >= 3:
                                print(GeometryCollection(_out).wkt)
                                sys.exit()
                            """

                            print(GeometryCollection(_out).wkt)
                        else:
                            print('LINESTRING EMPTY')
                        print(out)
                    else:

                        _temp = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                        _out = _temp

                        #print_period(_temp)

                        #id0, id1, id2, id3 = get_idx(MSEG[2], MSEG[3], LENMS, LETRI)
                        #print(LENMS, LETRI, MSEG[2], MSEG[3], id0, id1, id2, id3)

                        _temp = get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                        _out += _temp

                        #print_period(_temp)

                        #id0, id1, id2, id3 = get_idx(MSEG1[2], MSEG1[3], LENMS, LETRI)
                        #print(LENMS, LETRI, MSEG1[2], MSEG1[3], id0, id1, id2, id3)

                        _temp = get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                        _out += _temp

                        #print_period(_temp)

                        #id0, id1, id2, id3 = get_idx(MSEG2[2], MSEG2[3], LENMS, LETRI)
                        #print(LENMS, LETRI, MSEG2[2], MSEG2[3], id0, id1, id2, id3)
                        #sys.exit()

                        """
                        if len(_out) >= 3:
                            print(GeometryCollection(_out).wkt)
                            sys.exit()
                        """

                        print(GeometryCollection(_out).wkt)
                        print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    print(mline0.wkt)
                    #print(mline1.wkt)
                    print(GeometryCollection([mline1, mline2, mline3]).wkt)

                    if flag:
                        if out == 1:
                            _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                            _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                            _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                            print(GeometryCollection(_out).wkt)
                        else:
                            print('LINESTRING EMPTY')

                        print(out)
                    else:
                        _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                        _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                        _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                        print(GeometryCollection(_out).wkt)
                        print(1)

                    k += 1

                    eq = True

        if not eq:
            print(mline0.wkt)
            #print(mline1.wkt)
            print(GeometryCollection([mline1, mline2, mline3]).wkt)

            if out == 1:
                _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                print(GeometryCollection(_out).wkt)
            else:
                print('LINESTRING EMPTY')
            print(out)
        else:
            eq = False

def get_i(II, MSEG, reg_dict, t):
    IDICT = {}
    _m = len(II)
    _u = 0

    while _u < _m:
        _P = II[_u]

        for _I in _P:
            if isinstance(_I, Interval) and _I.contains(t):
                id_seg_reg = MSEG[_u][2]
                id_seg_tri = MSEG[_u][3]

                if id_seg_tri in IDICT:
                    e = IDICT[id_seg_tri]
                    e += [[id_seg_reg, _I, 0]]
                else:
                    IDICT[id_seg_tri] = [[id_seg_reg, _I, 0]]

                if id_seg_reg in reg_dict:
                    e = reg_dict[id_seg_reg]
                    e += [[id_seg_tri, _I, 0]]
                else:
                    reg_dict[id_seg_reg] = [[id_seg_tri, _I, 0]]

        _u += 1
    return IDICT

def get_i2(II, MSEG, reg_dict, t, L):
    IDICT = {}
    _m = len(II)
    _u = 0

    while _u < _m:
        _P = II[_u]

        for _I in _P:
            if isinstance(_I, Interval) and _I.contains(t):
                id_seg_reg = MSEG[_u][2]
                id_seg_tri = MSEG[_u][3]

                L += [[id_seg_tri, id_seg_reg, _u, 0]]

                if id_seg_tri in IDICT:
                    e = IDICT[id_seg_tri]
                    e += [[id_seg_reg, _I, len(L) - 1]]
                else:
                    IDICT[id_seg_tri] = [[id_seg_reg, _I, len(L) - 1]]

                if id_seg_reg in reg_dict:
                    e = reg_dict[id_seg_reg]
                    e += [[id_seg_tri, _I, len(L) - 1]]
                else:
                    reg_dict[id_seg_reg] = [[id_seg_tri, _I, len(L) - 1]]

        _u += 1
    return IDICT

def get_i3(II, MSEG, reg_dict, t):
    IDICT = {}
    _m = len(II)
    _u = 0

    while _u < _m:
        _P = II[_u]

        for _I in _P:
            if isinstance(_I, Interval) and _I.contains(t):
                id_seg_reg = MSEG[_u][2]
                id_seg_tri = MSEG[_u][3]

                v = Values(_u, 0)

                if id_seg_reg in IDICT:
                    e = IDICT[id_seg_reg]
                    e += v
                else:
                    IDICT[id_seg_reg] = v

                if id_seg_reg in reg_dict:
                    e = reg_dict[id_seg_reg]
                    e += [[id_seg_tri, v]]
                else:
                    reg_dict[id_seg_reg] = [[id_seg_tri, v]]

        _u += 1
    return IDICT

def get_i4(II, MSEG, t, reverse = False):
    _m = len(II)
    _u = 0

    IT = []

    if reverse:
        while _u < _m:
            _P = II[_u]

            for _I in _P:
                if isinstance(_I, Interval) and ((_I.contains(t) and not abs(t - _I.begin()) < 0.000000001) or abs(t - _I.end()) < 0.000000001):
                    id_seg_reg = MSEG[_u][2]
                    id_seg_tri = MSEG[_u][3]

                    #print(_I.to_string(), t, id_seg_reg, id_seg_tri, abs(t - _I.end()), )

                    x, y = get_it_point(id_seg_tri, _u, t, MSEG)
                    #IT += [(id_seg_reg, _u, x, y, shapely.geometry.Point(x, y))]
                    IT += [(id_seg_reg, id_seg_tri, _u, shapely.geometry.Point(x, y))]

            _u += 1
    else:
        while _u < _m:
            _P = II[_u]

            for _I in _P:
                if isinstance(_I, Interval) and ((_I.contains(t) and not abs(t - _I.end()) < 0.000000001) or abs(t - _I.begin()) < 0.000000001):
                    id_seg_reg = MSEG[_u][2]
                    id_seg_tri = MSEG[_u][3]

                    #print(_I.to_string(), t, id_seg_reg, id_seg_tri, abs(t - _I.end()), )

                    x, y = get_it_point(id_seg_tri, _u, t, MSEG)
                    #IT += [(id_seg_reg, _u, x, y, shapely.geometry.Point(x, y))]
                    IT += [(id_seg_reg, id_seg_tri, _u, shapely.geometry.Point(x, y))]

            _u += 1

    return IT

def get_i5(II, MSEG, t0, t1, reverse = False):
    _m = len(II)
    _u = 0

    IT = []

    if reverse:
        while _u < _m:
            _P = II[_u]

            for _I in _P:
                if isinstance(_I, Interval) and ((_I.contains(t0) and not abs(t0 - _I.begin()) < 0.000000001) or abs(t0 - _I.end()) < 0.000000001):
                    id_seg_reg = MSEG[_u][2]
                    id_seg_tri = MSEG[_u][3]

                    x, y = get_it_point(id_seg_tri, _u, t0, MSEG)
                    x1, y1 = get_it_point(id_seg_tri, _u, (t0 + t1) / 2, MSEG)
                    IT += [(id_seg_reg, id_seg_tri, _u, shapely.geometry.Point(x, y), shapely.geometry.Point(x1, y1))]

            _u += 1
    else:
        while _u < _m:
            _P = II[_u]

            for _I in _P:
                if isinstance(_I, Interval) and ((_I.contains(t0) and not abs(t0 - _I.end()) < 0.000000001) or abs(t0 - _I.begin()) < 0.000000001):
                    id_seg_reg = MSEG[_u][2]
                    id_seg_tri = MSEG[_u][3]

                    x, y = get_it_point(id_seg_tri, _u, t0, MSEG)
                    x1, y1 = get_it_point(id_seg_tri, _u, (t0 + t1) / 2, MSEG)
                    IT += [(id_seg_reg, id_seg_tri, _u, shapely.geometry.Point(x, y), shapely.geometry.Point(x1, y1))]

            _u += 1

    return IT

def get_it_point(s_id, u, t, MSEG):
    f = None

    """
    f = globals()["get_x%s" % u]
    x = f(t)
    y = get_yy(MSEG[u][1], t, x)
    """

    if s_id == 0:
        f = globals()["get_x%s" % u]
        x = f(t)
        y = get_yy(MSEG[u][1], t, x)
    elif s_id == 1:
        f = globals()["get_xx%s" % u]
        x = f(t)
        y = get_yy(MSEG[u][1], t, x)
    elif s_id == 2:
        f = globals()["get_xxx%s" % u]
        x = f(t)
        y = get_yy(MSEG[u][1], t, x)
    else:
        return None, None


    return x, y

def get_geom(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, level = 1):
    global DEBUG

    if level > 0 and t_s_id == ini and r_seg_id == ini_seg_id:
        return []

    #level = 1

    u = v.u
    v.v = 1

    if DEBUG:
        print('0', r_seg_id, t_s_id, ini, level)

    # segments intersection point
    if t_s_id == 0:
        x, y = get_it_point(t_s_id, u, t, MSEG)
    elif t_s_id == 1:
        x, y = get_it_point(t_s_id, u, t, MSEG1)
    elif t_s_id == 2:
        x, y = get_it_point(t_s_id, u, t, MSEG2)

    coords = [(x, y)]

    #print(x, y)

    # segment endpoint ccw
    p0 = t_s_id
    p1 = t_s_id + 1

    if p1 == N:
        p1 = 0

    # segment endpoint intersects (not) the region
    p1_in = False
    p0_in = False
    #assuming only 1 unit (TODO)
    if p1 == 0:
        p1_in = i1[0].contains(t)
        if p1_in:
            x1, y1 = mpoint1.at(t)
    elif p1 == 1:
        p1_in = i2[0].contains(t)
        if p1_in:
            x1, y1 = mpoint2.at(t)
    elif p1 == 2:
        p1_in = i3[0].contains(t)
        if p1_in:
            x1, y1 = mpoint3.at(t)

    if p0 == 0:
        p0_in = i1[0].contains(t)
    elif p0 == 1:
        p0_in = i2[0].contains(t)
    elif p0 == 2:
        p0_in = i3[0].contains(t)

    #print(r_seg_id, t_s_id, ini, p1_in, p1)

    several_it = False

    x0 = None
    y0 = None

    V = None
    if t_s_id == 0:
        for r_seg_id1 in _IDICT:
            v = _IDICT[r_seg_id1]

            if v.v == 0:
                several_it = True
                u = v.u
                x0, y0 = get_it_point(t_s_id, u, t, MSEG)
                V = v
                break
    elif t_s_id == 1:
        for r_seg_id1 in _IDICT1:
            v = _IDICT1[r_seg_id1]

            if v.v == 0:
                several_it = True
                u = v.u
                x0, y0 = get_it_point(t_s_id, u, t, MSEG1)
                V = v
                break
    elif t_s_id == 2:
        for r_seg_id1 in _IDICT2:
            v = _IDICT2[r_seg_id1]

            if v.v == 0:
                several_it = True
                u = v.u
                x0, y0 = get_it_point(t_s_id, u, t, MSEG2)
                V = v
                break

    if DEBUG:
        print(r_seg_id, r_seg_id1, t_s_id, ini, p0_in, p0, p1_in, p1)

    # if endpoint intersects the region
    """
    if not p0_in and not p1_in and several_it:
        coords += [(x0, y0)]
        V.u = 1
        #print('A')
    """
    if p1_in and not several_it:
        loop = True

        while loop:
            if DEBUG:
                print('B')
            #print('bbbbbbbbb')
            # add intersection point
            coords += [(x1, y1)]

            # find next segment ccw
            t_s_id = t_s_id + 1

            if t_s_id == N:
                t_s_id = 0

            if DEBUG:
                print(t_s_id, ini)

            if t_s_id == ini and level > 0:# and r_seg_id == ini_seg_id:
                if DEBUG:
                    print('end B')
                return coords
            elif t_s_id == 0:
                for r_seg_id in _IDICT:
                    v = _IDICT[r_seg_id]

                    if v.v == 0:
                        return coords + get_geom(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id)
                        #return coords + get_geom(t_s_id, v, t, MSEG, N, ini)
            elif t_s_id == 1:
                for r_seg_id in _IDICT1:
                    v = _IDICT1[r_seg_id]

                    if v.v == 0:
                        return coords + get_geom(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id)
                        #return coords + get_geom(t_s_id, v, t, MSEG1, N, ini)
            elif t_s_id == 2:
                for r_seg_id in _IDICT2:
                    v = _IDICT2[r_seg_id]

                    if v.v == 0:
                        return coords + get_geom(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id)
                        #return coords + get_geom(t_s_id, v, t, MSEG2, N, ini)

            level = 1
            p1 = t_s_id + 1

            if p1 == N:
                p1 = 0

            #assuming only 1 unit (TODO)
            if p1 == 0:
                x1, y1 = mpoint1.at(t)
            elif p1 == 1:
                x1, y1 = mpoint2.at(t)
            elif p1 == 2:
                x1, y1 = mpoint3.at(t)
    else:
        #if p0_in
        loop = True

        if DEBUG:
            print('C', r_seg_id, t_s_id, ini)

        while loop:
            #print(r_seg_id)
            #print('a', r_seg_id)
            #for r in _reg_dict:
            #    print(_reg_dict[r], r)

            L = []

            if r_seg_id in _reg_dict:
                L = _reg_dict[r_seg_id]

            for e in L:
                t_s_id = e[0]
                v = e[1]

                if DEBUG:
                    print(r_seg_id, t_s_id, ini, level)

                if t_s_id == ini and r_seg_id == ini_seg_id:
                    if level == 0:
                        if DEBUG:
                            print('continue')
                        continue

                    if DEBUG:
                        print('end')
                    return coords
                elif v.v == 0:
                    return coords + get_geom(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id)

            level = 1
            ms = MS[r_seg_id]
            x1, y1, x2, y2 = ms.at(t)
            coords += [(x2, y2)]

            r_seg_id = r_seg_id + 1
            if r_seg_id == len(MS):
                r_seg_id = 0

"""
def follow_r_boundary(r_seg_id, _reg_dict, t_s_id):
    global DEBUG

    loop = True

    if DEBUG:
        print('C', r_seg_id, t_s_id, ini)

    while loop:
        L = []

        if r_seg_id in _reg_dict:
            L = _reg_dict[r_seg_id]

        for e in L:
                t_s_id = e[0]
                v = e[1]

                if DEBUG:
                    print(r_seg_id, t_s_id, ini, level)

                if t_s_id == ini and r_seg_id == ini_seg_id:
                    if level == 0:
                        if DEBUG:
                            print('continue')
                        continue

                    if DEBUG:
                        print('end')
                    return coords
                elif v.v == 0:
                    return coords + get_geom(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id)

            level = 1
            ms = MS[r_seg_id]
            x1, y1, x2, y2 = ms.at(t)
            coords += [(x2, y2)]

            r_seg_id = r_seg_id + 1
            if r_seg_id == len(MS):
                r_seg_id = 0
"""

def get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, points, level = 1):
    global DEBUG

    if level > 0 and t_s_id == ini and r_seg_id == ini_seg_id:
        return []

    #level = 1

    u = v.u
    v.v = 1

    if DEBUG:
        print('0', r_seg_id, t_s_id, ini, level)

    # segments intersection point
    if t_s_id == 0:
        x, y = get_it_point(t_s_id, u, t, MSEG)
    elif t_s_id == 1:
        x, y = get_it_point(t_s_id, u, t, MSEG1)
    elif t_s_id == 2:
        x, y = get_it_point(t_s_id, u, t, MSEG2)

    coords = [(x, y)]

    # segment endpoint ccw

    p0 = t_s_id
    p1 = t_s_id + 1

    if p1 == N:
        p1 = 0

    p0_in = points[p0][0]
    p1_in = points[p1][0]

    x0 = None
    y0 = None

    V = None

    several_it = False
    next_r_seg_id = None
    follow_r_b = False

    if t_s_id == 0:
        for next_r_seg_id in _IDICT:
            v = _IDICT[next_r_seg_id]

            if v.v == 0:
                several_it = True
                u = v.u
                x0, y0 = get_it_point(t_s_id, u, t, MSEG)
                V = v
                break
    elif t_s_id == 1:
        for next_r_seg_id in _IDICT1:
            v = _IDICT1[next_r_seg_id]

            if v.v == 0:
                several_it = True
                u = v.u
                x0, y0 = get_it_point(t_s_id, u, t, MSEG1)
                V = v
                break
    elif t_s_id == 2:
        for next_r_seg_id in _IDICT2:
            v = _IDICT2[next_r_seg_id]

            if v.v == 0:
                several_it = True
                u = v.u
                x0, y0 = get_it_point(t_s_id, u, t, MSEG2)
                V = v
                break

    if DEBUG:
        print(r_seg_id, next_r_seg_id, t_s_id, ini, p0_in, p0, p1_in, p1)

    # Enter
    if not p0_in:
        if several_it:
            # follow seg to next intersection
            coords += [(x0, y0)]
            V.v = 1
            # follow boundary of the region, next_r_seg_id
            r_seg_id = next_r_seg_id
            follow_r_b = True
        #else:
        #   follow seg
    # Leave
    else:
        follow_r_b = True
        points[p0][0] = False

    # follow boundary of the region
    if follow_r_b:
        loop = True

        if DEBUG:
            print('FRB', r_seg_id, t_s_id, ini)

        while loop:
            L = []

            if r_seg_id in _reg_dict:
                L = _reg_dict[r_seg_id]

            for e in L:
                t_s_id = e[0]
                v = e[1]

                if DEBUG:
                    print(r_seg_id, t_s_id, ini, level)

                if t_s_id == ini and r_seg_id == ini_seg_id:
                    if level == 0:
                        if DEBUG:
                            print('continue')

                        continue

                    if DEBUG:
                        print('end')

                    return coords
                elif v.v == 0:
                    return coords + get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, points)

            level = 1
            ms = MS[r_seg_id]
            x1, y1, x2, y2 = ms.at(t)
            coords += [(x2, y2)]

            r_seg_id = r_seg_id + 1
            if r_seg_id == len(MS):
                r_seg_id = 0
    else:
        loop = True

        x1 = points[p1][1]
        y1 = points[p1][2]

        while loop:
            if DEBUG:
                print('FS')

            coords += [(x1, y1)]

            # find next segment ccw
            t_s_id = t_s_id + 1

            if t_s_id == N:
                t_s_id = 0

            if DEBUG:
                print(t_s_id, ini)

            if t_s_id == ini and level > 0:
                if DEBUG:
                    print('end FS')

                return coords
            elif t_s_id == 0:
                for r_seg_id in _IDICT:
                    v = _IDICT[r_seg_id]

                    if v.v == 0:
                        return coords + get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, points)
            elif t_s_id == 1:
                for r_seg_id in _IDICT1:
                    v = _IDICT1[r_seg_id]

                    if v.v == 0:
                        return coords + get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, points)
            elif t_s_id == 2:
                for r_seg_id in _IDICT2:
                    v = _IDICT2[r_seg_id]

                    if v.v == 0:
                        return coords + get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, points)

            level = 1
            p1 = t_s_id + 1

            if p1 == N:
                p1 = 0

            x1 = points[p1][1]
            y1 = points[p1][2]

def get_geoms_it(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, points, level = 1):
    global DEBUG

    u = v.u

    # segments intersection point
    if t_s_id == 0:
        x, y = get_it_point(t_s_id, u, t, MSEG)
    elif t_s_id == 1:
        x, y = get_it_point(t_s_id, u, t, MSEG1)
    elif t_s_id == 2:
        x, y = get_it_point(t_s_id, u, t, MSEG2)

    coords = [(x, y)]

    # segment endpoint ccw

    p0 = t_s_id
    p1 = t_s_id + 1

    if p1 == N:
        p1 = 0

    p0_in = points[p0][0]
    p1_in = points[p1][0]

    x0 = None
    y0 = None

    V = None

    several_it = False
    next_r_seg_id = None
    follow_r_b = False

    if t_s_id == 0:
        for next_r_seg_id in _IDICT:
            v = _IDICT[next_r_seg_id]

            if v.v == 0:
                several_it = True
                u = v.u
                x0, y0 = get_it_point(t_s_id, u, t, MSEG)
                V = v
                break
    elif t_s_id == 1:
        for next_r_seg_id in _IDICT1:
            v = _IDICT1[next_r_seg_id]

            if v.v == 0:
                several_it = True
                u = v.u
                x0, y0 = get_it_point(t_s_id, u, t, MSEG1)
                V = v
                break
    elif t_s_id == 2:
        for next_r_seg_id in _IDICT2:
            v = _IDICT2[next_r_seg_id]

            if v.v == 0:
                several_it = True
                u = v.u
                x0, y0 = get_it_point(t_s_id, u, t, MSEG2)
                V = v
                break

    if DEBUG:
        print(r_seg_id, next_r_seg_id, t_s_id, ini, p0_in, p0, p1_in, p1)

    # Enter
    if not p0_in:
        if several_it:
            # follow seg to next intersection
            coords += [(x0, y0)]
            V.v = 1
            # follow boundary of the region, next_r_seg_id
            r_seg_id = next_r_seg_id
            follow_r_b = True
        #else:
        #   follow seg
    # Leave
    else:
        follow_r_b = True
        points[p0][0] = False

    # follow boundary of the region
    if follow_r_b:
        loop = True

        if DEBUG:
            print('FRB', r_seg_id, t_s_id, ini)

        while loop:
            L = []

            if r_seg_id in _reg_dict:
                L = _reg_dict[r_seg_id]

            for e in L:
                t_s_id = e[0]
                v = e[1]

                if DEBUG:
                    print(r_seg_id, t_s_id, ini, level)

                if t_s_id == ini and r_seg_id == ini_seg_id:
                    if level == 0:
                        if DEBUG:
                            print('continue')

                        continue

                    if DEBUG:
                        print('end')

                    return coords
                elif v.v == 0:
                    return coords + get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, points)

            level = 1
            ms = MS[r_seg_id]
            x1, y1, x2, y2 = ms.at(t)
            coords += [(x2, y2)]

            r_seg_id = r_seg_id + 1
            if r_seg_id == len(MS):
                r_seg_id = 0
    else:
        loop = True

        x1 = points[p1][1]
        y1 = points[p1][2]

        while loop:
            if DEBUG:
                print('FS')

            coords += [(x1, y1)]

            # find next segment ccw
            t_s_id = t_s_id + 1

            if t_s_id == N:
                t_s_id = 0

            if DEBUG:
                print(t_s_id, ini)

            if t_s_id == ini and level > 0:
                if DEBUG:
                    print('end FS')

                return coords
            elif t_s_id == 0:
                for r_seg_id in _IDICT:
                    v = _IDICT[r_seg_id]

                    if v.v == 0:
                        return coords + get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, points)
            elif t_s_id == 1:
                for r_seg_id in _IDICT1:
                    v = _IDICT1[r_seg_id]

                    if v.v == 0:
                        return coords + get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, points)
            elif t_s_id == 2:
                for r_seg_id in _IDICT2:
                    v = _IDICT2[r_seg_id]

                    if v.v == 0:
                        return coords + get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, N, i1, i2, i3, mpoint1, mpoint2, mpoint3, ini, ini_seg_id, points)

            level = 1
            p1 = t_s_id + 1

            if p1 == N:
                p1 = 0

            x1 = points[p1][1]
            y1 = points[p1][2]

def get_points_data(i1, i2, i3, mpoint1, mpoint2, mpoint3, t):
    points = []
    p_in = False

    #px = 0
    #py = 0

    p_in = i1[0].contains(t)
    if p_in:
        px, py = mpoint1.at(t)
        points += [[0, shapely.geometry.Point(px, py)]]

    #px = 0
    #py = 0

    p_in = i2[0].contains(t)
    if p_in:
        px, py = mpoint2.at(t)
        points += [[1, shapely.geometry.Point(px, py)]]

    #points += [[p_in, px, py, shapely.geometry.Point(px, py)]]

    px = 0
    py = 0

    p_in = i3[0].contains(t)
    if p_in:
        px, py = mpoint3.at(t)
        points += [[2, shapely.geometry.Point(px, py)]]

    #points += [[p_in, px, py, shapely.geometry.Point(px, py)]]

    return points

def get_points_data2(i1, i2, i3, mpoint1, mpoint2, mpoint3, t, t1):
    points = []
    p_in = False

    #px = 0
    #py = 0

    p_in = i1[0].contains(t) and i1[0].contains(t1)
    if p_in:
        px, py = mpoint1.at(t)
        px1, py1 = mpoint1.at(t1)
        points += [[0, shapely.geometry.Point(px, py), shapely.geometry.Point(px1, py1)]]

    #px = 0
    #py = 0

    p_in = i2[0].contains(t) and i2[0].contains(t1)
    if p_in:
        px, py = mpoint2.at(t)
        px1, py1 = mpoint2.at(t1)
        points += [[1, shapely.geometry.Point(px, py), shapely.geometry.Point(px1, py1)]]

    #points += [[p_in, px, py, shapely.geometry.Point(px, py)]]

    px = 0
    py = 0

    p_in = i3[0].contains(t) and i3[0].contains(t1)
    if p_in:
        px, py = mpoint3.at(t)
        px1, py1 = mpoint3.at(t1)
        points += [[2, shapely.geometry.Point(px, py), shapely.geometry.Point(px1, py1)]]

    #points += [[p_in, px, py, shapely.geometry.Point(px, py)]]

    return points

def get_i_period(arr_intersection_periods):
    P = []
	
    for intersection_period in arr_intersection_periods:
        for period in intersection_period:
            for intersection in period:
                # interval
                if isinstance(intersection, Interval):
                    if P == []:
                        P += [[intersection, 1]]
                    else:
                        L = []
                        N = len(P)
                        J = 0

                        inserted = False

                        while J < N:
                            e = P[J]
                            i = e[0]
                            #n = e[1]

                            # new intersection is before an already existing one.
                            if intersection.end() <= i.begin():
                                L += [[intersection, 1]]
                                L += [e]
                                
                                J += 1
                                inserted = True

                                while J < N:
                                    L += [P[J]]
                                    J += 1

                                break
                            # new intersection intersects an already existing one.
                            elif not (intersection.end() <= i.begin() or i.end() <= intersection.begin()):
                                if intersection.begin() == i.begin() and intersection.end() == i.end():
                                    e[1] += 1
                                    L += [e]

                                    J += 1
                                    inserted = True

                                    # add the other elements.
                                    while J < N:
                                        L += [P[J]]
                                        J += 1

                                    break
                                elif intersection.begin() == i.begin():
                                    if intersection.end() < i.end():
                                        L += [[Interval(intersection.begin(), intersection.end(), True, True), e[1] + 1]]
                                        L += [[Interval(intersection.end(), i.end(), True, True), e[1]]]

                                        J += 1
                                        inserted = True

                                        # add the other elements.
                                        while J < N:
                                            L += [P[J]]
                                            J += 1

                                        break
                                    else:
                                        L += [[Interval(intersection.begin(), i.end(), True, True), e[1] + 1]]
                                        intersection = Interval(i.end(), intersection.end(), True, True)
                                        J += 1
                                elif intersection.end() == i.end():
                                    if intersection.begin() < i.begin():
                                        L += [[Interval(intersection.begin(), i.begin(), True, True), 1]]
                                        L += [[Interval(i.begin(), i.end(), True, True), e[1] + 1]]
                                    else:
                                        L += [[Interval(i.begin(), intersection.begin(), True, True), e[1]]]
                                        L += [[Interval(intersection.begin(), intersection.end(), True, True), e[1] + 1]]

                                    J += 1
                                    inserted = True

                                    # add the other elements.
                                    while J < N:
                                        L += [P[J]]
                                        J += 1

                                    break
                                else:
                                    if intersection.begin() < i.begin():
                                        if intersection.end() < i.end():
                                            L += [[Interval(intersection.begin(), i.begin(), True, True), 1]]
                                            L += [[Interval(i.begin(), intersection.end(), True, True), e[1] + 1]]
                                            L += [[Interval(intersection.end(), i.end(), True, True), e[1]]]

                                            J += 1
                                            inserted = True

                                            # add the other elements.
                                            while J < N:
                                                L += [P[J]]
                                                J += 1

                                            break
                                        else:
                                            L += [[Interval(intersection.begin(), i.begin(), True, True), 1]]
                                            L += [[Interval(i.begin(), i.end(), True, True), e[1] + 1]]

                                            intersection = Interval(i.end(), intersection.end(), True, True)

                                            J += 1
                                    else:
                                        if intersection.end() < i.end():
                                            L += [[Interval(i.begin(), intersection.begin(), True, True), e[1]]]
                                            L += [[Interval(intersection.begin(), intersection.end(), True, True), e[1] + 1]]
                                            L += [[Interval(intersection.end(), i.end(), True, True), e[1]]]

                                            J += 1
                                            inserted = True

                                            # add the other elements.
                                            while J < N:
                                                L += [P[J]]
                                                J += 1

                                            break
                                        else:
                                            L += [[Interval(i.begin(), intersection.begin(), True, True), e[1]]]
                                            L += [[Interval(intersection.begin(), i.end(), True, True), e[1] + 1]]

                                            intersection = Interval(i.end(), intersection.end(), True, True)

                                            J += 1
                            else:
                                L += [e]
                                J += 1

                        # insert intersection at the end.
                        if not inserted:
                            L += [[intersection, 1]]

                        P = L

                # instant
                #else:
                #    print(e)

    return P

def get_geoms(MS, it, mpoint1, mpoint2, mpoint3):
    P = get_region_at(MS, it.x)
    Q = get_region_at(MS, it.y)

    coords = []

    x, y = mpoint1.at(it.x)
    coords += [(x, y)]

    x, y = mpoint2.at(it.x)
    coords += [(x, y)]

    x, y = mpoint3.at(it.x)
    coords += [(x, y)]

    coords += [(coords[0][0], coords[0][1])]

    geom1 = Polygon(coords)

    coords = []

    x, y = mpoint1.at(it.y)
    coords += [(x, y)]

    x, y = mpoint2.at(it.y)
    coords += [(x, y)]

    x, y = mpoint3.at(it.y)
    coords += [(x, y)]

    coords += [(coords[0][0], coords[0][1])]

    geom2 = Polygon(coords)

    return P, Q, geom1, geom2, P.intersection(geom1), Q.intersection(geom2)

def get_points_inside_period(L):
    N = len(L)

    if L == None or N == 0:
        return []
    elif N == 1:
        return L[0]

    inside = L[0]
    j = 1

    while j < N:
        inside = intersect_periods2(inside, L[j])
        j += 1

    return inside

def get_seg_i_period(L):
    it = []

    for I in L:
        n = len(I)
        iterator = 0

        if len(it) == 0 and n > 0:
            it = I[0]
            iterator = 1

        while iterator < n:
            it = union_periods(it, I[iterator])
            iterator += 1

    return it

def get_unit_regions_inside(MS, mpoint1, mpoint2, mpoint3, inside_period):
    for t in inside_period:
        if isinstance(t, Interval):
            p, Q, G1, G2, INT1, INT2 = get_geoms(MS, t, mpoint1, mpoint2, mpoint3)
            print(t.to_string(), 'all')
            #print(p.wkt + ';')
            #print(Q.wkt + ';')
            #print(G1.wkt + ';')
            #print(G2.wkt + ';')
            print(INT1.wkt + ';')
            print(INT2.wkt + ';')
            print('')
        else:
            print(t)

def get_triangle_at(mpoint1, mpoint2, mpoint3, t):
    coords = []

    x, y = mpoint1.at(t)
    coords += [(x, y)]

    x, y = mpoint2.at(t)
    coords += [(x, y)]

    x, y = mpoint3.at(t)
    coords += [(x, y)]

    coords += [(coords[0][0], coords[0][1])]

    return Polygon(coords)

def get_corr(reg0, reg1, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT1, IT2, IT3, t, reverse = False):
    Geometries = []
    eps = 0.00001
    spatial_eps = 0.000000001

    points = get_points_data(i1, i2, i3, mpoint1, mpoint2, mpoint3, t)

    it = reg0.intersection(reg1)

    #print(reg0.wkt + ';')
    #print(reg1.wkt + ';')
    #print(it.wkt + ';')

    # no intersection (unexpected)
    if it.is_empty:
        Points = []
        for it in IT1:
            #print(it)
            Points += [it]
        for it in IT2:
            #print(it)
            Points += [it]
        for it in IT3:
            #print(it)
            Points += [it]
        #for point in points:
        #    print(point)

        # two intersections at a point
        if len(Points) == 2:
            if abs(Points[0][3].distance(Points[1][3])) < eps:
                coords2 = reg0.exterior.coords
                M = len(coords2) - 1
                j = 0
                corr = []
                corr += [[(-1, 1, -1, Points[0])]]
                corr += [[(-1, 1, -1, Points[1])]]

                x_avg = (Points[0][3].x + Points[1][3].x) / 2
                y_avg = (Points[0][3].y + Points[1][3].y) / 2

                p = shapely.geometry.Point(x_avg, y_avg)

                while j < M:
                    x = coords2[j][0]
                    y = coords2[j][1]

                    p1 = shapely.geometry.Point(x, y)

                    d = p1.distance(p)
                    if d < eps:
                        corr += [[(-1, 2, d, [j, p1])]]

                    j += 1
                return [corr], []
            else:
                return [], []
        else:
            return [], []

        """
        print('')

        print(abs(Points[0].distance(Points[1])))
        for p in Points:
            print(p.wkt)

        return [], []
        """

        #print('ERR: No intersection found!', 'get_corr()')
        #sys.exit()
    # geometry
    elif it.geom_type == 'Polygon' or it.geom_type == 'Point' or it.geom_type == 'LineString':
        Geometries += [it]
    # collection
    elif it.geom_type == 'GeometryCollection' or it.geom_type == 'MultiPolygon' or it.geom_type == 'MultiPoint' or it.geom_type == 'MultiLineString':
        for geom in it:
            Geometries += [geom]
    # unexpected type of geometry
    else:
        print(it.geom_type, 'get_corr()', 'TODO')
        sys.exit()

    CORR = []

    for geom in Geometries:
        coords = geom.exterior.coords
        N = len(coords) - 1
        i = 0

        C = [(coords[i][0], coords[i][1])]
        i = 1

        while i < N:
            x0 = coords[i-1][0]
            y0 = coords[i-1][1]
            p0 = shapely.geometry.Point(x0, y0)

            x = coords[i][0]
            y = coords[i][1]
            p1 = shapely.geometry.Point(x, y)

            if p0.distance(p1) > spatial_eps:
                C += [(x, y)]

            i += 1

        C += [(C[0][0], C[0][1])]

        #coords = geom.exterior.coords
        coords = C
        N = len(coords) - 1
        i = 0

        corr = []

        while i < N:
            found = False

            x = coords[i][0]
            y = coords[i][1]
            p = shapely.geometry.Point(x, y)

            #print('>>>>>>>>>>>>>>>>>>>>>>>')
            #print(x, y, N, p.wkt + ';')
            #print('>>>>>>>>>>>>>>>>>>>>>>>')

            for point in points:
                d = point[1].distance(p)
                if d < eps:
                    #print(i, 0, d, point, '--------------------------')
                    corr += [[(i, 0, d, point)]]
                    found = True
                    #break

            #if found:
            #    i += 1
            #    continue

            for it in IT1:
                d = it[3].distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]
                        c += [(i, 1, d, it)]
                    else:
                        corr += [[(i, 1, d, it)]]

                    found = True
                    #break

            #if found:
            #    i += 1
            #    continue

            for it in IT2:
                d = it[3].distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]
                        c += [(i, 1, d, it)]
                    else:
                        corr += [[(i, 1, d, it)]]

                    #corr += [(i, 1, it)]
                    found = True
                    #break

            #if found:
            #    i += 1
            #    continue

            for it in IT3:
                d = it[3].distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]
                        c += [(i, 1, d, it)]
                    else:
                        corr += [[(i, 1, d, it)]]

                    #corr += [(i, 1, it)]
                    found = True
                    #break

            #if found:
            #    i += 1
            #    continue

            if reverse:
                coords2 = reg1.exterior.coords
            else:
                coords2 = reg0.exterior.coords

            M = len(coords2) - 1
            j = 0

            while j < M:
                x = coords2[j][0]
                y = coords2[j][1]

                p1 = shapely.geometry.Point(x, y)

                d = p1.distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]
                        c += [(i, 2, d, [j, p1])]
                    else:
                        corr += [[(i, 2, d, [j, p1])]]

                    #corr += [(i, 2, [j, p1])]
                    found = True
                    #break

                j += 1

            # if there is more than one correspondence, choose the one with the smallest distance
            # >>>>>
            c = corr[len(corr) - 1]
            if len(c) > 1:
                v = c[0]
                #print(c)
                #print(v)
                iterator = 1

                while iterator < len(c):
                    # choose smaller distance.
                    if c[iterator][2] < v[2]:
                        v = c[iterator]

                    iterator += 1

                #print(v)
                corr[len(corr) - 1] = [v]
            # >>>>>

            i += 1

        CORR += [corr]

    return CORR, Geometries

def get_corr2(reg0, reg1, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT1, IT2, IT3, t, t1, reverse, reg2, reg3):
    Geometries = []

    # some thresholds
    eps = 0.00001
    spatial_eps = 0.000000001
    area_eps = 0.000000001

    #points = get_points_data(i1, i2, i3, mpoint1, mpoint2, mpoint3, t)
    points = get_points_data2(i1, i2, i3, mpoint1, mpoint2, mpoint3, t, (t + t1) / 2)

    it = reg0.intersection(reg1)
    #it = reg3.intersection(reg2)
    regIT = it
    #if not it.is_empty:
    #    it = shapely.geometry.polygon.orient(it)

    # no intersection (unexpected)
    if it.is_empty:
        Points = []
        for it in IT1:
            Points += [it]
        for it in IT2:
            Points += [it]
        for it in IT3:
            Points += [it]

        # two intersections at a point
        if len(Points) == 2:
            if abs(Points[0][3].distance(Points[1][3])) < eps:
                coords2 = reg0.exterior.coords
                M = len(coords2) - 1
                j = 0
                corr = []
                corr += [[(-1, 1, -1, Points[0])]]
                corr += [[(-1, 1, -1, Points[1])]]

                x_avg = (Points[0][3].x + Points[1][3].x) / 2
                y_avg = (Points[0][3].y + Points[1][3].y) / 2

                p = shapely.geometry.Point(x_avg, y_avg)

                while j < M:
                    x = coords2[j][0]
                    y = coords2[j][1]

                    p1 = shapely.geometry.Point(x, y)

                    d = p1.distance(p)
                    if d < eps:
                        corr += [[(-1, 2, d, [j, p1])]]

                    j += 1
                return [corr], [], [], [0]
            else:
                return [], [], [], [0]
        else:
            return [], []
    # geometry
    elif it.geom_type == 'Polygon' or it.geom_type == 'Point' or it.geom_type == 'LineString':
        it = shapely.geometry.polygon.orient(it)
        Geometries += [it]
    # collection
    elif it.geom_type == 'GeometryCollection' or it.geom_type == 'MultiPolygon' or it.geom_type == 'MultiPoint' or it.geom_type == 'MultiLineString':
        for geom in it:
            it = shapely.geometry.polygon.orient(geom)
            Geometries += [geom]
    # unexpected type of geometry
    else:
        print(it.geom_type, 'get_corr()', 'TODO')
        sys.exit()

    CORR = []
    ALT = []
    NALT = []

    for geom in Geometries:
        # eliminate similar points
        coords = geom.exterior.coords
        N = len(coords) - 1
        i = 0

        C = [(coords[i][0], coords[i][1])]
        i = 1

        while i < N:
            x0 = coords[i-1][0]
            y0 = coords[i-1][1]
            p0 = shapely.geometry.Point(x0, y0)

            x = coords[i][0]
            y = coords[i][1]
            p1 = shapely.geometry.Point(x, y)

            if p0.distance(p1) > spatial_eps:
                C += [(x, y)]

            i += 1

        C += [(C[0][0], C[0][1])]

        # end

        n_alternatives = 0

        # find correspondence
        #coords = C
        coords = geom.exterior.coords
        N = len(coords) - 1
        i = 0

        corr = []
        

        while i < N:
            found = False
            n_sim_vertices = 0

            x = coords[i][0]
            y = coords[i][1]
            p = shapely.geometry.Point(x, y)

            for point in points:
                d = point[1].distance(p)
                if d < eps:
                    corr += [[(i, 0, d, point)]]
                    found = True

            for it in IT1:
                d = it[3].distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]
                        c += [(i, 1, d, it)]
                        n_sim_vertices += 1
                    else:
                        corr += [[(i, 1, d, it)]]

                    found = True

            for it in IT2:
                d = it[3].distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]
                        c += [(i, 1, d, it)]
                        n_sim_vertices += 1
                    else:
                        corr += [[(i, 1, d, it)]]

                    found = True

            for it in IT3:
                d = it[3].distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]
                        c += [(i, 1, d, it)]
                        n_sim_vertices += 1
                    else:
                        corr += [[(i, 1, d, it)]]

                    found = True

            if reverse:
                coords2 = reg1.exterior.coords
            else:
                coords2 = reg0.exterior.coords

            M = len(coords2) - 1
            j = 0

            while j < M:
                x = coords2[j][0]
                y = coords2[j][1]

                p1 = shapely.geometry.Point(x, y)

                d = p1.distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]

                        if reg2.contains(p):
                            c += [(i, 2, d, [j, p1])]
                            n_sim_vertices += 1

                        """
                        add = True
                        if len(c) == 2:
                            if c[0][1] == 1 and c[1][1] == 1:
                                add = False
                                #c += [(i, 2, d, [j, p1])]

                        if add:
                            c += [(i, 2, d, [j, p1])]
                            n_sim_vertices += 1
                        """

                        #c += [(i, 2, d, [j, p1])]
                        #n_sim_vertices += 1
                    else:
                        corr += [[(i, 2, d, [j, p1])]]

                    found = True

                j += 1

            if n_sim_vertices > n_alternatives:
                n_alternatives = n_sim_vertices

            # find right order for the points in the correspondence
            if corr != []:
                c = corr[len(corr) - 1]
                #print(c)
                #print(len(coords))

                if len(c) > 1:
                    v = c[0]
                    iterator = 1

                    while iterator < len(c):
                        # choose smaller distance.
                        if c[iterator][2] < v[2]:
                            v = c[iterator]

                        iterator += 1

                    corr[len(corr) - 1] = [v]
                # >>>>>
            """
            else:
                # static point
                if geom.area < area_eps:
                    corr += [[(i, 2, d, [j, p1])]]
                print(reg0.wkt + ';')
                print(reg1.wkt + ';')
                print(geom.wkt + ';', geom.area)
                print(regIT.wkt + ';')
            """

            i += 1

        if n_alternatives == 1:
            ncorr = []
            for c in corr:
                if len(c) == 1:
                    ncorr += [c]
                elif len(c) == 2:
                    ncorr += [[c[1], c[0]]]
                else:
                    print('Unexpected num of similar vertices.', len(c))
                    ncorr += [c]

            ALT += [ncorr]
        elif n_alternatives == 2:
            #0, 1, 2
            #0, 2, 1
            perm = []
            ncorr = []
            for c in corr:
                if len(c) == 1:
                    ncorr += [c]
                elif len(c) == 2:
                    ncorr += [[c[1], c[0]]]
                elif len(c) == 3:
                    ncorr += [[c[1], c[0]]]
                else:
                    print('Two many similar vertices.', len(c))
                    ncorr += [c]
                    #sys.exit()

            ALT += [ncorr]
        elif n_alternatives > 2:
            print('Two many similar vertices.', n_alternatives)

        if corr == [] and geom.area < area_eps:
            corr += [[(-1, 3, -1, geom)]]

        CORR += [corr]
        NALT += [n_alternatives]

    return CORR, Geometries, ALT, NALT

def get_corr3(reg0, reg1, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT1, IT2, IT3, t, t1, reverse, reg2, reg3):
    Geometries = []

    # some thresholds
    eps = 0.00001
    spatial_eps = 0.000000001
    area_eps = 0.000000001

    #points = get_points_data(i1, i2, i3, mpoint1, mpoint2, mpoint3, t)
    points = get_points_data2(i1, i2, i3, mpoint1, mpoint2, mpoint3, t, (t + t1) / 2)

    #it = reg0.intersection(reg1)
    it = reg3.intersection(reg2)
    #regIT = it

    #if not it.is_empty:
    #    it = shapely.geometry.polygon.orient(it)

    # no intersection (unexpected)
    if it.is_empty:
        """
        Points = []
        for it in IT1:
            Points += [it]
        for it in IT2:
            Points += [it]
        for it in IT3:
            Points += [it]

        # two intersections at a point
        if len(Points) == 2:
            if abs(Points[0][3].distance(Points[1][3])) < eps:
                coords2 = reg0.exterior.coords
                M = len(coords2) - 1
                j = 0
                corr = []
                corr += [[(-1, 1, -1, Points[0])]]
                corr += [[(-1, 1, -1, Points[1])]]

                x_avg = (Points[0][3].x + Points[1][3].x) / 2
                y_avg = (Points[0][3].y + Points[1][3].y) / 2

                p = shapely.geometry.Point(x_avg, y_avg)

                while j < M:
                    x = coords2[j][0]
                    y = coords2[j][1]

                    p1 = shapely.geometry.Point(x, y)

                    d = p1.distance(p)
                    if d < eps:
                        corr += [[(-1, 2, d, [j, p1])]]

                    j += 1
                return [corr], [], [], [0]
            else:
                return [], [], [], [0]
        else:
            return [], []
        """
        print(it.geom_type, 'EMPTY', 'UNEXPECTED')
        sys.exit()
    # geometry
    elif it.geom_type == 'Polygon' or it.geom_type == 'Point' or it.geom_type == 'LineString':
        it = shapely.geometry.polygon.orient(it)
        Geometries += [it]
    # collection
    elif it.geom_type == 'GeometryCollection' or it.geom_type == 'MultiPolygon' or it.geom_type == 'MultiPoint' or it.geom_type == 'MultiLineString':
        for geom in it:
            it = shapely.geometry.polygon.orient(geom)
            Geometries += [geom]
    # unexpected type of geometry
    else:
        print(it.geom_type, 'get_corr()', 'TODO')
        sys.exit()

    CORR = []
    ALT = []
    NALT = []

    for geom in Geometries:
        n_alternatives = 0

        # find correspondence
        #coords = C
        coords = geom.exterior.coords
        N = len(coords) - 1
        i = 0

        corr = []
        idx = 4        
        while i < N:
            found = False
            #n_sim_vertices = 0

            x = coords[i][0]
            y = coords[i][1]
            p = shapely.geometry.Point(x, y)

            for point in points:
                d = point[2].distance(p)
                if d < eps:
                    corr += [[(i, 0, d, point)]]
                    found = True

            for it in IT1:
                d = it[idx].distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]
                        c += [(i, 1, d, it)]
                        #n_sim_vertices += 1
                    else:
                        corr += [[(i, 1, d, it)]]

                    found = True

            for it in IT2:
                d = it[idx].distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]
                        c += [(i, 1, d, it)]
                        #n_sim_vertices += 1
                    else:
                        corr += [[(i, 1, d, it)]]

                    found = True

            for it in IT3:
                d = it[idx].distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]
                        c += [(i, 1, d, it)]
                        #n_sim_vertices += 1
                    else:
                        corr += [[(i, 1, d, it)]]

                    found = True

            #if reverse:
            #    coords2 = reg1.exterior.coords
            #else:
            #    coords2 = reg0.exterior.coords

            coords2 = reg3.exterior.coords

            M = len(coords2) - 1
            j = 0

            while j < M:
                x = coords2[j][0]
                y = coords2[j][1]

                p1 = shapely.geometry.Point(x, y)

                d = p1.distance(p)
                if d < eps:
                    if found:
                        c = corr[len(corr) - 1]

                        if reg2.contains(p):
                            c += [(i, 2, d, [j, p1])]
                            #n_sim_vertices += 1
                    else:
                        corr += [[(i, 2, d, [j, p1])]]

                    found = True

                j += 1

            #if n_sim_vertices > n_alternatives:
            #    n_alternatives = n_sim_vertices

            # find right order for the points in the correspondence
            """
            if corr != []:
                c = corr[len(corr) - 1]
                #print(c)
                #print(len(coords))

                if len(c) > 1:
                    v = c[0]
                    iterator = 1

                    while iterator < len(c):
                        # choose smaller distance.
                        if c[iterator][2] < v[2]:
                            v = c[iterator]

                        iterator += 1

                    corr[len(corr) - 1] = [v]
                # >>>>>
            """

            i += 1

        """
        if n_alternatives == 1:
            ncorr = []
            for c in corr:
                if len(c) == 1:
                    ncorr += [c]
                elif len(c) == 2:
                    ncorr += [[c[1], c[0]]]
                else:
                    print('Unexpected num of similar vertices.', len(c))
                    ncorr += [c]

            ALT += [ncorr]
        elif n_alternatives == 2:
            #0, 1, 2
            #0, 2, 1
            perm = []
            ncorr = []
            for c in corr:
                if len(c) == 1:
                    ncorr += [c]
                elif len(c) == 2:
                    ncorr += [[c[1], c[0]]]
                elif len(c) == 3:
                    ncorr += [[c[1], c[0]]]
                else:
                    print('Two many similar vertices.', len(c))
                    ncorr += [c]
                    #sys.exit()

            ALT += [ncorr]
        elif n_alternatives > 2:
            print('Two many similar vertices.', n_alternatives)
        """

        if corr == [] and geom.area < area_eps:
            corr += [[(-1, 3, -1, geom)]]

        CORR += [corr]
        NALT += [n_alternatives]

    return CORR, Geometries, ALT, NALT

def get_value_at(mpoint1, mpoint2, mpoint3, reg, MSEG, MSEG1, MSEG2, v, data, t):
    point = None

    # point in the triangle
    if v == 0:
        pid = data[0]
										
        if pid == 0:
            x, y = mpoint1.at(t)
        elif pid == 1:
            x, y = mpoint2.at(t)
        elif pid == 2:
            x, y = mpoint3.at(t)

        point = shapely.geometry.Point(x, y)
    # intersection
    elif v == 1:
        rid = data[0]
        pid = data[1]
        u = data[2]

        if pid == 0:
            x, y = get_it_point(pid, u, t, MSEG)
        elif pid == 1:
            x, y = get_it_point(pid, u, t, MSEG1)
        elif pid == 2:
            x, y = get_it_point(pid, u, t, MSEG2)

        point = shapely.geometry.Point(x, y)
    # region boundary
    elif v == 2:
        pid = data[0]
        _coords = reg.exterior.coords
        x = _coords[pid][0]
        y = _coords[pid][1]

        point = shapely.geometry.Point(x, y)

    return point

def get_order(coordinates):
    P = [(0, 1, 2)]
    P += [(0, 2, 1)]
    P += [(1, 0, 2)]
    P += [(1, 2, 0)]
    P += [(2, 1, 0)]
    P += [(2, 0, 1)]

    for p in P:
        x1 = coordinates[p[0]][0]
        y1 = coordinates[p[0]][1]
        x2 = coordinates[p[1]][0]
        y2 = coordinates[p[1]][1]
        x3 = coordinates[p[2]][0]
        y3 = coordinates[p[2]][1]

        A = x1 * (y2-y3 ) + x2 * (y3-y1 ) + x3 * (y1-y2)
        if A < 0:
            return p

    return None

def coords_to_ccw(coords):
    ccw_coords = []
    lc = [coords[0], coords[1], coords[2]]

    o = get_order(lc)
    if o == None:
        print('W-ORDER')
        sys.exit()

    ccw_coords += [lc[o[0]]]
    ccw_coords += [lc[o[1]]]
    ccw_coords += [lc[o[2]]]

    N = len(coords)
    i = 3

    while i < N:
        lc = [coords[i-2], coords[i-1], coords[i]]
        ccw_coords += [coords[i]]

        o = get_order(lc)
        if o == None:
            print('W-ORDER')
            sys.exit()

        ccw_coords[i-2] = lc[o[0]]
        ccw_coords[i-1] = lc[o[1]]
        ccw_coords[i] = lc[o[2]]

        i += 1

    return ccw_coords

def get_coords(el, mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, t0, t1):
    coords0 = []
    coords1 = []
    coords2 = []

    prev_p0 = None
    prev_p1 = None
    prev_p2 = None

    count = 0
    eps = 0.000001

    for l in el:
        for v in l:
            u = v[3]
            type = v[1]

            if type == 3:
                return u.exterior.coords, u.exterior.coords, u.exterior.coords

            p0 = u[len(u) - 1]
            p1 = get_value_at(mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, type, u, t1)
            p2 = get_value_at(mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, type, u, (t0 + t1) / 2)

            if count > 0:
                #print(prev_p0.distance(p0), 'd')
                if prev_p0.distance(p0) > eps:
                    coords0 += [(p0.x, p0.y)]
                    prev_p0 = p0
                else:
                    coords0[len(coords0) - 1] = ((prev_p0.x + p0.x) / 2, (prev_p0.y + p0.y) / 2)

                if prev_p1.distance(p1) > eps:
                    coords1 += [(p1.x, p1.y)]
                    prev_p1 = p1
                else:
                    coords1[len(coords1) - 1] = ((prev_p1.x + p1.x) / 2, (prev_p1.y + p1.y) / 2)

                if prev_p2.distance(p2) > eps:
                    coords2 += [(p2.x, p2.y)]
                    prev_p2 = p2
                else:
                    coords2[len(coords2) - 1] = ((prev_p2.x + p2.x) / 2, (prev_p2.y + p2.y) / 2)
            else:
                coords0 += [(p0.x, p0.y)]
                coords1 += [(p1.x, p1.y)]
                coords2 += [(p2.x, p2.y)]

                prev_p0 = p0
                prev_p1 = p1
                prev_p2 = p2

            #print(u[len(u) - 1].wkt + ';', p1.wkt + ';', l)
            #print(u[len(u) - 1].wkt + ';', p1.wkt + ';')
            count += 1

    coords0 += [(coords0[0][0], coords0[0][1])]
    coords1 += [(coords1[0][0], coords1[0][1])]
    coords2 += [(coords2[0][0], coords2[0][1])]

    return coords0, coords1, coords2

def change_coord(coords, corr, eps, idx):
    x1 = coords[0][0]
    y1 = coords[0][1]

    np = len(coords) - 1

    x2 = coords[np][0]
    y2 = coords[np][1]

    d = shapely.geometry.Point(x1, y1).distance(shapely.geometry.Point(x2, y2))

    if d < eps:
        x = (x1 + x2) / 2
        y = (y1 + y2) / 2

        alist = []
        i = 0

        while i < np:
            alist += [coords[i]]
            i += 1

        coords = alist
        coords[0] = (x, y)

        ntp = None
        tp = corr[len(corr) - 1]

        if idx == 0:
            ntp = (0, tp[1], tp[2])
        else:
            ntp = (tp[0], tp[1], 0)

        corr[len(corr) - 1] = ntp

    return coords

#def get_coords2(el, mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, t0, t1):
def get_coords2(el, mpoint1, mpoint2, mpoint3, reg0, reg1, reg2, MSEG, MSEG1, MSEG2, t0, t1):
    coords0 = []
    coords1 = []
    coords2 = []

    MSIDS = []

    prev_p0 = None
    prev_p1 = None
    prev_p2 = None

    count = 0
    eps = 0.000001
    #eps = 0.00000001

    u = None
    type = None

    id1 = -1
    id2 = -1
    id3 = -1

    for l in el:
        for v in l:
            u = v[3]
            type = v[1]

            if type == 3:
                return u.exterior.coords, u.exterior.coords, u.exterior.coords, []

            #p0 = u[len(u) - 1]
            p0 = get_value_at(mpoint1, mpoint2, mpoint3, reg0, MSEG, MSEG1, MSEG2, type, u, t0)
            p1 = get_value_at(mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, type, u, (t0 + t1) / 2)
            p2 = get_value_at(mpoint1, mpoint2, mpoint3, reg2, MSEG, MSEG1, MSEG2, type, u, t1)

            if count > 0:
                #print(prev_p0.distance(p0), 'd')

                if prev_p0.distance(p0) > eps:
                    coords0 += [(p0.x, p0.y)]
                    prev_p0 = p0
                else:
                    coords0[len(coords0) - 1] = ((prev_p0.x + p0.x) / 2, (prev_p0.y + p0.y) / 2)

                if prev_p2.distance(p2) > eps:
                    coords2 += [(p2.x, p2.y)]
                    prev_p2 = p2
                else:
                    coords2[len(coords2) - 1] = ((prev_p2.x + p2.x) / 2, (prev_p2.y + p2.y) / 2)

                #if prev_p2.distance(p2) > eps:
                coords1 += [(p1.x, p1.y)]
                #    prev_p2 = p2
                #else:
                #    coords2[len(coords2) - 1] = ((prev_p2.x + p2.x) / 2, (prev_p2.y + p2.y) / 2)

                id1 = len(coords0) - 1
                id2 = len(coords1) - 1					
                id3 = len(coords2) - 1
            else:
                coords0 += [(p0.x, p0.y)]
                coords1 += [(p1.x, p1.y)]
                coords2 += [(p2.x, p2.y)]

                prev_p0 = p0
                prev_p1 = p1
                prev_p2 = p2

                id1 = 0
                id2 = 0
                id3 = 0

            MSIDS += [(id1, id2, id3)]

            #print(u[len(u) - 1].wkt + ';', p1.wkt + ';', l)
            #print(u[len(u) - 1].wkt + ';', p1.wkt + ';')
            count += 1

    if len(coords0) > 2:
        coords0 = change_coord(coords0, MSIDS, eps, 0)
        coords0 += [(coords0[0][0], coords0[0][1])]

    if len(coords1) > 2:
        coords1 += [(coords1[0][0], coords1[0][1])]

    if len(coords2) > 2:
        coords2 = change_coord(coords2, MSIDS, eps, 2)
        coords2 += [(coords2[0][0], coords2[0][1])]

    return coords0, coords1, coords2, MSIDS

def get_geom_from_coords(coords):
    if len(coords) == 1:
        return shapely.geometry.Point(coords)
    elif len(coords) == 2:
        return shapely.geometry.LineString(coords)
    else:
        return Polygon(coords)

#get_samples_for_out7(MS, G, G1, G2, M, M1, M2, I, I1, I2, ms1, ms2, ms3, interval, n_samples, intersections, i1, i2, i3, mpoint1, mpoint2, mpoint3, reg_dict, IDICT, IDICT1, IDICT2)
def get_samples_for_out7(MS, G, G1, G2, MSEG, MSEG1, MSEG2, II, II1, II2, ms1, ms2, ms3, i, n_samples, s, i1, i2, i3, mpoint1, mpoint2, mpoint3, reg_dict, IDICT, IDICT1, IDICT2):
    global interval
    global pass_through_control_points
    global print_intersection_information
    global print_solver_execution_time
    global TESTING

    """
    p = loads('POLYGON ((874.9239798135775 701.664953008842, 842.3775939511288 699.9957656927584, 916.8573239071751 650.6371197496198, 897.6901823914855 694.711540008419, 895.8679296163343 693.5213232079568, 884.609356483609 690.693643738764, 875.6185912431511 688.2636689361013, 874.9239798135334 701.6649530089767, 874.9239798135775 701.664953008842))')

    CC = p.exterior.coords
    NN = len(CC)
    II = 0
    while II < NN - 1:
        x0 = CC[II][0]
        y0 = CC[II][1]

        x1 = CC[II+1][0]
        y1 = CC[II+1][1]

        d = shapely.geometry.Point(x0, y0).distance(shapely.geometry.Point(x1, y1))

        print(d, d > 0.000001)

        II += 1
    sys.exit()
    """

    P = get_i_period([II, II1, II2])

    region_points_inside_period = get_points_inside_period([i1, i2, i3])

    region_segs_intersection = get_seg_i_period([II, II1, II2])
    region_segs_no_intersection = complement_period(region_segs_intersection, interval)
    region_inside_period = intersection_periods(region_segs_no_intersection, region_points_inside_period)

    #print(region_points_inside_period)
    #print(region_segs_intersection)
    #print(region_segs_no_intersection)
    #print(region_inside_period)

    """
    id = 1
    for e in P:
        print(e[0].to_string(), e[1], id)
        id += 1
    """

    #sys.exit()

    gen_geoms = []
    count = 0

    mr = MovingRegion()
    units0 = []
    units1 = []

    for e in P:
        UI = e[0]
        #print(e, UI.to_string())
        #np = v[1]
        if isinstance(UI, Interval):
            """
            p, Q, G1, G2, INT1, INT2 = get_geoms(MS, e, mpoint1, mpoint2, mpoint3)
            print(e.to_string(), 'all')
            print(INT1.wkt + ';')
            print(INT2.wkt + ';')
            print('')
            """

            t0 = UI.begin()
            t1 = UI.end()

            #print(t0, t1)

            triangle0 = get_triangle_at(mpoint1, mpoint2, mpoint3, t0)
            triangle1 = get_triangle_at(mpoint1, mpoint2, mpoint3, t1)
            triangle2 = get_triangle_at(mpoint1, mpoint2, mpoint3, (t0 + t1) / 2)

            reg0 = get_region_at(MS, t0)
            reg1 = get_region_at(MS, t1)
            reg2 = get_region_at(MS, (t0 + t1) / 2)

            #print(reg0.wkt + ';')
            #print(reg1.wkt + ';')

            #print(triangle0.wkt + ';')
            #print(triangle1.wkt + ';')			

            """
            IT01 = get_i4(II, MSEG, t0)
            IT02 = get_i4(II1, MSEG1, t0)
            IT03 = get_i4(II2, MSEG2, t0)
            """

            IT01 = get_i5(II, MSEG, t0, t1)
            IT02 = get_i5(II1, MSEG1, t0, t1)
            IT03 = get_i5(II2, MSEG2, t0, t1)

            #C0, G0 = get_corr(reg0, triangle0, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT01, IT02, IT03, t0)

            #C0, G0, ALT, NALT = get_corr2(reg0, triangle0, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT01, IT02, IT03, t0, t1, False, triangle2, reg2)
            C0, G0, ALT, NALT = get_corr3(reg0, triangle0, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT01, IT02, IT03, t0, t1, False, triangle2, reg2)

            #for el in C0:
            #    print(el)

            """
            if G0 == []:
                IT11 = get_i4(II, MSEG, t1, True)
                IT12 = get_i4(II1, MSEG1, t1, True)
                IT13 = get_i4(II2, MSEG2, t1, True)

                C1, G1 = get_corr(reg1, triangle1, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT11, IT12, IT13, t1, True)
            """

            """
            for o in IT11:
                print(o, o[3].wkt + ';')
            for o in IT12:
                print(o, o[3].wkt + ';')
            for o in IT13:
                print(o, o[3].wkt + ';')

            print(reg1.wkt + ';')
            print(triangle1.wkt + ';')
            """

            #N = len(G0)
            #I = 0

            #gemos = []
            #gen_geoms = []
            counter = 0

            #print(len(C0))

            ur = MRU(UI)

            for el in C0:
                #print(el)
                #coords0, coords1, coords2, MSIDS = get_coords2(el, mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, t0, t1)
                coords0, coords1, coords2, MSIDS = get_coords2(el, mpoint1, mpoint2, mpoint3, reg0, reg2, reg1, MSEG, MSEG1, MSEG2, t0, t1)

                """
                coords0 = []
                coords1 = []
                coords2 = []
                for l in el:
                    for v in l:
                        u = v[3]
                        type = v[1]

                        p1 = get_value_at(mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, type, u, t1)
                        p2 = get_value_at(mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, type, u, (t0 + t1) / 2)
						
                        p0 = u[len(u) - 1]

                        coords0 += [(p0.x, p0.y)]
                        coords1 += [(p1.x, p1.y)]
                        coords2 += [(p2.x, p2.y)]

                        #print(u[len(u) - 1].wkt + ';', p1.wkt + ';', l)
                        #print(u[len(u) - 1].wkt + ';', p1.wkt + ';')

                coords0 += [(coords0[0][0], coords0[0][1])]
                coords1 += [(coords1[0][0], coords1[0][1])]
                coords2 += [(coords2[0][0], coords2[0][1])]
                """

                """
                if len(coords0) > 3:
                    coords0 = coords_to_ccw(coords0)

                if len(coords1) > 3:
                    coords1 = coords_to_ccw(coords1)

                if len(coords2) > 3:
                    coords2 = coords_to_ccw(coords2)
                """

                #print(coords0)
                DEB = ''
                if NALT[counter] > 1:
                    #print(el)
                    DEB = 'FFFFFFFFFFFFFFFFFFF'

                source_reg = get_geom_from_coords(coords0)
                target_reg = get_geom_from_coords(coords1)
                midlle_obs = get_geom_from_coords(coords2)

                """
                if len(coords0) == 1:
                    source_reg = shapely.geometry.Point(coords0)
                elif len(coords0) == 2:
                    source_reg = shapely.geometry.LineString(coords0)
                else:
                    source_reg = Polygon(coords0)

                if len(coords1) == 1:
                    target_reg = shapely.geometry.Point(coords1)
                elif len(coords1) == 2:
                    target_reg = shapely.geometry.LineString(coords1)
                else:
                    target_reg = Polygon(coords1)

                if len(coords2) == 1:
                    midlle_obs = shapely.geometry.Point(coords2)
                elif len(coords2) == 2:
                    midlle_obs = shapely.geometry.LineString(coords2)
                else:
                    midlle_obs = Polygon(coords2)
                """

                #source_reg = Polygon(coords0)
                #target_reg = Polygon(coords1)
                #midlle_obs = Polygon(coords2)
                """
                if len(ALT) > 0 and (not source_reg.is_valid or not target_reg.is_valid):
                    elm = ALT[counter]
                    coords0, coords1, coords2, MSIDS = get_coords2(elm, mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, t0, t1)

                    source_reg = get_geom_from_coords(coords0)
                    target_reg = get_geom_from_coords(coords1)
                    midlle_obs = get_geom_from_coords(coords2)
                """
                #if len(C0) == 2:
                #    print(source_reg.wkt + ';')

                counter += 1
                gen_geoms += [(source_reg, target_reg, UI, reg0, reg1, triangle0, triangle1, midlle_obs, DEB, el)]

                """
                print('')
                for elem in MSIDS:
                    print(elem)
                print('')
                """

                IMS = []
                msu = []

                Z = 1
                E = len(MSIDS)

                #for elem in MSIDS:
                while Z < E:
                    un = []

                    id1 = coords0[MSIDS[Z-1][0]]
                    id2 = coords1[MSIDS[Z-1][1]]
                    id3 = coords2[MSIDS[Z-1][2]]

                    id4 = coords0[MSIDS[Z][0]]
                    id5 = coords1[MSIDS[Z][1]]
                    id6 = coords2[MSIDS[Z][2]]

                    x1 = id1[0]
                    y1 = id1[1]

                    x2 = id2[0]
                    y2 = id2[1]

                    x3 = id3[0]
                    y3 = id3[1]

                    x4 = id4[0]
                    y4 = id4[1]

                    x5 = id5[0]
                    y5 = id5[1]

                    x6 = id6[0]
                    y6 = id6[1]

                    un += [[x1, y1, x2, y2, x3, y3], [x4, y4, x5, y5, x6, y6]]
                    un += [UI.begin(), UI.end()]
                    un = [un, [UI.begin(), UI.end()]]
                    msu += [un]
                    #un += [[x1, y1, x2, y2, x3, y3], [x4, y4, x5, y5, x6, y6]]

                    Z += 1

                #un += [UI.begin(), UI.end()]
                #un = [un, [UI.begin(), UI.end()]]

                """
                un = []

                print(coords0, MSIDS[E-1][0], len(MSIDS))

                id1 = coords0[MSIDS[E-1][0]]
                id2 = coords1[MSIDS[E-1][1]]
                id3 = coords2[MSIDS[E-1][2]]

                id4 = coords0[MSIDS[0][0]]
                id5 = coords1[MSIDS[0][1]]
                id6 = coords2[MSIDS[0][2]]

                x1 = id1[0]
                y1 = id1[1]

                x2 = id2[0]
                y2 = id2[1]

                x3 = id3[0]
                y3 = id3[1]

                x4 = id4[0]
                y4 = id4[1]

                x5 = id5[0]
                y5 = id5[1]

                x6 = id6[0]
                y6 = id6[1]

                un += [[x1, y1, x2, y2, x3, y3], [x4, y4, x5, y5, x6, y6]]
                un += [UI.begin(), UI.end()]
                un = [un, [UI.begin(), UI.end()]]
                msu += [un]
                """

                #print(un)
                for u in msu:
                    IMS += [create_moving_segment2([], pass_through_control_points, [u])]

                # p, q, ms
                ur.add_p(source_reg)
                ur.add_q(reg1.intersection(triangle1))
                ur.add_ms(IMS)

            """
            if count == 12:
                #print(ur.p)
                #print(ur.q)
                #print(ur.ms)
                #print(UI.to_string())
                #print(source_reg.wkt + ';')
                #print(reg1.intersection(triangle1).wkt + ';')

                print(reg0.wkt + ';')
                print(triangle0.wkt + ';')
                print(reg2.wkt + ';')
                print(triangle2.wkt + ';')
                print(reg1.wkt + ';')

                print('')
                geom = ur.at(UI.begin())
                print(geom.wkt + ';')
                geom = ur.at((UI.begin() + UI.end()) / 2)
                print(geom.wkt + ';')
                geom = ur.at(((UI.begin() + UI.end()) / 2 + UI.end()) / 2)
                print(geom.wkt + ';')
                geom = ur.at(UI.end())
                print(geom.wkt + ';')
                print('')

                print(el)
                #sys.exit()
            """

            #mr.add_unit(ur)
            units0 += [ur]

            """
            if G0 == []:
                for el in C1:
                    coords0 = []
                    coords1 = []
                    coords2 = []
                    for l in el:
                        for v in l:
                            u = v[3]
                            type = v[1]

                            p0 = get_value_at(mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, type, u, t0)
                            p2 = get_value_at(mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2, type, u, (t0 + t1) / 2)

                            p1 = u[len(u) - 1]

                            coords0 += [(p0.x, p0.y)]
                            coords1 += [(p1.x, p1.y)]
                            coords2 += [(p2.x, p2.y)]

                            #print(u[len(u) - 1].wkt + ';', p1.wkt + ';', l)
                            #print(u[len(u) - 1].wkt + ';', p1.wkt + ';')

                    coords0 += [(coords0[0][0], coords0[0][1])]
                    coords1 += [(coords1[0][0], coords1[0][1])]
                    coords2 += [(coords2[0][0], coords2[0][1])]

                    source_reg = Polygon(coords0)
                    target_reg = Polygon(coords1)
                    midlle_obs = Polygon(coords2)

                    #gen_geoms += [(source_reg, target_reg, UI)]
                    gen_geoms += [(source_reg, target_reg, UI, reg0, reg1, triangle0, triangle1, midlle_obs)]
            """
        else:
            print(UI, 'TODO')

        count += 1
        #if count == 2:
        #    break

    # inside the region
    for e in region_inside_period:
        if isinstance(e, Interval):
            #print(e.to_string(), '--')
            coords0 = []
            coords1 = []
            coords2 = []

            ur = MRU(e)

            t = e.begin()
            x, y = mpoint1.at(t)
            coords0 += [(x, y)]
            x, y = mpoint2.at(t)
            coords0 += [(x, y)]
            x, y = mpoint3.at(t)
            coords0 += [(x, y)]
            coords0 += [(coords0[0][0], coords0[0][1])]

            t = (e.begin() + e.end()) / 2
            x, y = mpoint1.at(t)
            coords1 += [(x, y)]
            x, y = mpoint2.at(t)
            coords1 += [(x, y)]
            x, y = mpoint3.at(t)
            coords1 += [(x, y)]
            coords1 += [(coords1[0][0], coords1[0][1])]

            t = e.end()
            x, y = mpoint1.at(t)
            coords2 += [(x, y)]
            x, y = mpoint2.at(t)
            coords2 += [(x, y)]
            x, y = mpoint3.at(t)
            coords2 += [(x, y)]
            coords2 += [(coords2[0][0], coords2[0][1])]

            msu = []
            E = len(coords2)
            Z = 0
            while Z < E:
                un = []

                id1 = coords0[Z-1]
                id2 = coords1[Z-1]
                id3 = coords2[Z-1]

                id4 = coords0[Z]
                id5 = coords1[Z]
                id6 = coords2[Z]

                x1 = id1[0]
                y1 = id1[1]

                x2 = id2[0]
                y2 = id2[1]

                x3 = id3[0]
                y3 = id3[1]

                x4 = id4[0]
                y4 = id4[1]

                x5 = id5[0]
                y5 = id5[1]

                x6 = id6[0]
                y6 = id6[1]

                un += [[x1, y1, x2, y2, x3, y3], [x4, y4, x5, y5, x6, y6]]
                un += [e.begin(), e.end()]
                un = [un, [e.begin(), e.end()]]
                msu += [un]

                Z += 1

            UMS = []
            for u in msu:
                UMS += [create_moving_segment2([], pass_through_control_points, [u])]

            ur.add_p(Polygon(coords0))
            ur.add_q(Polygon(coords2))
            ur.add_ms(UMS)

            units1 += [ur]
        else:
            print(e, 'all: todo')

    #print(len(mr.get_units()))

    K0 = len(units0)
    K1 = len(units1)

    #print(K0, K1)
    #sys.exit()

    iK0 = 0
    iK1 = 0

    while iK0 < K0 and iK1 < K1:
        u0 = units0[iK0]
        u1 = units1[iK1]

        if u0.i.end() <= u1.i.begin():
            mr.add_unit(u0)
            iK0 += 1
        else:
            mr.add_unit(u1)
            iK1 += 1

    while iK0 < K0:
        u0 = units0[iK0]

        mr.add_unit(u0)
        iK0 += 1

    while iK1 < K1:
        u1 = units1[iK1]

        mr.add_unit(u1)
        iK1 += 1

    n_invalid_geoms = 0
    n_complex_geoms = 0

    # use this for specific testing
    #n_samples = 100
    #get_samples_for_vout2(MS, mr, mpoint1, mpoint2, mpoint3, interval, n_samples)

    proc_end_exec_time = time.time()

    # use this for production
    n_samples = 1500
    n_invalid_geoms, n_complex_geoms = get_samples_for_vout(MS, mr, mpoint1, mpoint2, mpoint3, interval, n_samples)

    return proc_end_exec_time, n_invalid_geoms, n_complex_geoms, len(mr.units)

    #for u in mr.get_units():
    #    print(u.i.to_string())

    #sys.exit()

    #print(len(mr.get_units()), len(mr.get_units()) * 100)
    #counter = 0

    """
    counter = 0
    for u in mr.get_units():
        #if counter == 13:
        get_obs_from_unit(u, n_samples, 1)

        print(counter)
        #counter += 1
        counter += 1
        #if counter == 5:
        #    break
    """

    if print_intersection_information:
        print('Regions Intersection: N_INVALID_GEOMS: ' + str(n_invalid_geoms) + ', N_COMPLEX_GEOMS: ' + str(n_complex_geoms))

    if print_solver_execution_time:
        print("Exec. Time: "+ "-1" + "sec, NE: " + "-1")

    sys.exit()
	
	
	
	
	
    unit_id = 0

    for v in gen_geoms:

        s_reg = v[0]
        t_reg = v[1]
        mobs = v[7]
        deb = v[8]
        el = v[9]

        i = v[2]

        r0 = v[3]
        r1 = v[4]
        tri0 = v[5]
        tri1 = v[6]

        print('')
        #print(el)
        print(unit_id, i.to_string(), s_reg.is_valid, s_reg.is_simple, t_reg.is_valid, t_reg.is_simple, mobs.is_valid, mobs.is_simple, deb)

        print(r0.wkt + ';')
        print(tri0.wkt + ';')
        print(s_reg.wkt + ';')
        print('')
        print(r1.wkt + ';')
        print(tri1.wkt + ';')
        print(t_reg.wkt + ';')
        print('')
        print(s_reg.wkt + ';')
        print(mobs.wkt + ';')
        print(t_reg.wkt + ';')

        print('')

        unit_id += 1

    if print_intersection_information:
        print('Regions Intersection')

    if print_solver_execution_time:
        print("Exec. Time: "+ "-1" + "sec, NE: " + "-1")

    #print('')
    #return
    sys.exit()

    # ///////////////////////////////////////////////////////////////
    # ///////////////////////////////////////////////////////////////
    # ///////////////////////////////////////////////////////////////

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
    i1_len = len(i1)
    i2_len = len(i2)
    i3_len = len(i3)
    i1_idx = 0
    i2_idx = 0
    i3_idx = 0

    LENMS = len(MS)
    LETRI = 3

    """
    print_i_periods(II)
    print_i_periods(II1)
    print_i_periods(II2)
    sys.exit()
    """

    for j in range(0, n_samples):
        t = i.x + dt * (float(j) / n)
        t01 = (t - i.x) / dt
        out = 0
        flag = False

        #mpoint1_in = False
        #mpoint2_in = False

        #mpoint1_pos = None
        #mpoint2_pos = None

        if J < N and t >= T[J]:
            t = T[J]
            t01 = (t - i.x) / dt
            out = K[J]
            J += 1
            flag = True

        mline0 = get_region_at(MS, t)
        mline1 = ms1.obj_at(t)
        mline2 = ms2.obj_at(t)
        mline3 = ms3.obj_at(t)

        #print(GeometryCollection([mline1, mline2, mline3]).wkt)

        coll = []
        geoms = []

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    print(mline0.wkt)
                    #print(mline1.wkt)
                    print(GeometryCollection([mline1, mline2, mline3]).wkt)

                    if flag:
                        if out == 1:
                            _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                            _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                            _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)

                            """
                            if len(_out) >= 3:
                                print(GeometryCollection(_out).wkt)
                                sys.exit()
                            """

                            print(GeometryCollection(_out).wkt)
                        else:
                            print('LINESTRING EMPTY')
                        print(out)
                    else:
                        #####
                        """
                        for e in II:
                            print(e)
                        """

                        #reg_dict, IDICT, IDICT1, IDICT2

                        _reg_dict = {}

                        """
                        L = []

                        _IDICT = get_i2(II, MSEG, _reg_dict, t, L)
                        _IDICT1 = get_i2(II1, MSEG1, _reg_dict, t, L)
                        _IDICT2 = get_i2(II2, MSEG2, _reg_dict, t, L)
                        """

                        P = get_i_period([II, II1, II2])

                        #inside = intersect_periods(i1, i2)
                        #inside = intersect_periods(inside, i3)

                        # no intersections intersection inside
                        #inside = intersect_periods2(i1, i2)
                        #inside = intersect_periods2(inside, i3)

                        region_points_inside_period = get_points_inside_period([i1, i2, i3])

                        """
                        for e in inside:
                            if isinstance(e, Interval):
                                print(e.to_string())
                            else:
                                print(e)

                        print('')

                        for e in inside1:
                            if isinstance(e, Interval):
                                print(e.to_string())
                            else:
                                print(e)

                        print('')
                        """

                        #union_periods(i1, i2)

                        """
                        num = len(II)
                        iterator = 1
                        seg_it = []

                        if num > 0:
                            seg_it = II[0]

                        while iterator < num:
                            seg_it = union_periods(seg_it, II[iterator])
                            iterator += 1

                        num = len(II1)
                        iterator = 0

                        if len(seg_it) == 0 and num > 0:
                            seg_it = II1[0]
                            iterator = 1

                        while iterator < num:
                            seg_it = union_periods(seg_it, II1[iterator])
                            iterator += 1

                        num = len(II2)
                        iterator = 0

                        if len(seg_it) == 0 and num > 0:
                            seg_it = II2[0]
                            iterator = 1

                        while iterator < num:
                            seg_it = union_periods(seg_it, II2[iterator])
                            iterator += 1
                        """

                        region_segs_intersection = get_seg_i_period([II, II1, II2])

                        """
                        print('')

                        for e in seg_it:
                            if isinstance(e, Interval):
                                print(e.to_string())
                            else:
                                print(e)

                        print('')

                        for e in seg_it1:
                            if isinstance(e, Interval):
                                print(e.to_string())
                            else:
                                print(e)

                        print('')

                        sys.exit()
                        """

                        """
                        for E in II:
                            inside1 = union_periods(inside1, E)

                            for e in E:
                                print(e, inside1)
                                inside1 = union_periods(inside1, e)
                        """

                        #inside1 = intersect_periods(II, II1)
                        #inside1 = intersect_periods(inside1, II2)
                        #inside = intersect_periods2(i1, i2)

                        region_segs_no_intersection = complement_period(region_segs_intersection, interval)
                        region_inside_period = intersection_periods(region_segs_no_intersection, region_points_inside_period)

                        triangle = get_triangle_at(mpoint1, mpoint2, mpoint3, t)

                        """
                        print('')

                        count = 0

                        for v in P:
                            it = v[0]
                            np = v[1]

                            if isinstance(it, Interval):
                                p, Q, G1, G2, INT1, INT2 = get_geoms(MS, it, mpoint1, mpoint2, mpoint3)

                                print(it.to_string(), np)
                                #print(p.wkt + ';')
                                #print(Q.wkt + ';')
                                #print(G1.wkt + ';')
                                #print(G2.wkt + ';')
                                print(INT1.wkt + ';')
                                print(INT2.wkt + ';')
                                print('')
                            else:
                                print(it, np)

                            if count == 2:
                                print(INT1.wkt + ';')

                            count += 1
                        print('')
                        """

                        # ...

                        #_IT1 = get_i4(II, MSEG, t)
                        #_IT2 = get_i4(II1, MSEG1, t)
                        #_IT3 = get_i4(II2, MSEG2, t)

                        t0 = 1085.51397674907
                        t1 = 1121.44916273651

                        triangle0 = get_triangle_at(mpoint1, mpoint2, mpoint3, t0)
                        triangle1 = get_triangle_at(mpoint1, mpoint2, mpoint3, t1)

                        reg0 = get_region_at(MS, t0)
                        reg1 = get_region_at(MS, t1)

                        IT01 = get_i4(II, MSEG, t0)
                        IT02 = get_i4(II1, MSEG1, t0)
                        IT03 = get_i4(II2, MSEG2, t0)

                        """
                        print('')
                        for u in IT01:
                            print(u, 1)
                        for u in IT02:
                            print(u, 2)
                        for u in IT03:
                            print(u, 3)
                        print('')

                        sys.exit()
                        """

                        IT11 = get_i4(II, MSEG, t1)
                        IT12 = get_i4(II1, MSEG1, t1)
                        IT13 = get_i4(II2, MSEG2, t1)

                        C0, G0 = get_corr(reg0, triangle0, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT01, IT02, IT03, t0)
                        C1, G1 = get_corr(reg1, triangle1, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT11, IT12, IT13, t1)

                        N = len(G0)
                        I = 0

                        gemos = []

                        #print(reg0.wkt + ';', triangle0.wkt + ';')
                        #print(reg1.wkt + ';', triangle1.wkt + ';')

                        #print('')
                        #print(C0)
                        #print(C1)

                        gen_geoms = []

                        for e in C0:
                            coords0 = []
                            coords1 = []
                            for l in e:
                                #print(l)
                                for v in l:
                                    #print(v)
                                    u = v[3]
                                    type = v[1]

                                    p1 = get_value_at(mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2,type, u, t1)
                                    #get_value_at(mpoint1, mpoint2, mpoint3, reg, MSEG, MSEG1, MSEG2, v, data, t)

                                    p0 = u[len(u) - 1]

                                    coords0 += [(p0.x, p0.y)]
                                    coords1 += [(p1.x, p1.y)]

                                    #print(u[len(u) - 1].wkt + ';', p1.wkt + ';', l)
                                    #print(u[len(u) - 1].wkt + ';', p1.wkt + ';')

                            coords0 += [(coords0[0][0], coords0[0][1])]
                            coords1 += [(coords1[0][0], coords1[0][1])]

                            #print(coords0)
                            #print(coords1)

                            source_reg = Polygon(coords0)
                            target_reg = Polygon(coords1)

                            gen_geoms += [(source_reg, target_reg)]

                        #source_reg = Polygon(coords0).buffer(0.0)
                        #target_reg = Polygon(coords1).buffer(0.0)

                        print('')
                        for unit_geoms in gen_geoms:
                            source_reg = unit_geoms[0]
                            target_reg = unit_geoms[1]

                            if not source_reg.is_valid:
                                print(source_reg.wkt + ';', 'Source not Valid.')

                            if not source_reg.is_simple:
                                print(source_reg.wkt + ';', 'Source not Simple.')

                            if not target_reg.is_valid:
                                print(target_reg.wkt + ';', 'Target not Valid.')

                            if not target_reg.is_simple:
                                print(target_reg.wkt + ';', 'Target not Simple.')

                            print(source_reg.wkt + ';')
                            print(target_reg.wkt + ';')
                        print('')

                        #gen_geoms += [source_reg]
                        #gen_geoms += [source_reg]						

                        """
                        print('')
                        for e in C0:
                            for l in e:
                                for v in l:
                                    u = v[2]
                                    type = v[1]

                                    point_at_t = get_value_at(mpoint1, mpoint2, mpoint3, reg1, MSEG, MSEG1, MSEG2,type, u, t1)
                                    #get_value_at(mpoint1, mpoint2, mpoint3, reg, MSEG, MSEG1, MSEG2, v, data, t)

                                    #print(u[len(u) - 1].wkt + ';', point_at_t.wkt + ';', l)
                                    print(u[len(u) - 1].wkt + ';', point_at_t.wkt + ';')

                        print('')
                        """

                        """
                        while I < N:
                            coords = G0[I].exterior.coords
                            corr = C0[I]

                            for c in corr:
                                M = len(coords) - 1
                                J = 0

                                print(c)
                                c = c[0]

                                while J < M:
                                    #coord_id = corr[J][0]
                                    coord_id = c[0]

                                    v = c[1]
                                    data = c[2]
                                    J += 1

                                    np = None

                                    # point
                                    if v == 0:
                                        pid = data[0]
										
                                        if pid == 0:
                                            x, y = mpoint1.at(t0)
                                        elif pid == 1:
                                            x, y = mpoint2.at(t0)
                                        elif pid == 2:
                                            x, y = mpoint3.at(t0)

                                        np = shapely.geometry.Point(x, y)
                                    # intersection
                                    elif v == 1:
                                        rid = data[0]
                                        pid = data[1]
                                        u = data[2]

                                        if pid == 0:
                                            x, y = get_it_point(pid, u, t0, MSEG)
                                        elif pid == 1:
                                            x, y = get_it_point(pid, u, t0, MSEG1)
                                        elif pid == 2:
                                            x, y = get_it_point(pid, u, t0, MSEG2)

                                        np = shapely.geometry.Point(x, y)
                                    # region boundary
                                    elif v == 2:
                                        pid = data[0]
                                        _coords = reg0.exterior.coords
                                        x = _coords[pid][0]
                                        y = _coords[pid][1]

                                        np = shapely.geometry.Point(x, y)

                                    #gemos += [data[len(data)-1].wkt]
                                    gemos += [np]

                            I += 1


                        print('')
                        for g in gemos:
                            print(g.wkt + ';')
                        print('')
                        """

                        #for g in it:
                        #    G += [g]

                        """
                        print('')
                        for g in G0:
                            print(g.wkt + ';')

                        print('')

                        print('')
                        for g in G1:
                            print(g.wkt + ';')

                        print('')

                        print('')
                        for c in C0:
                            print(c)

                        print('')
                        for c in C1:
                            print(c)

                        print('')

                        """

                        #it = Interval(t0, t1, True, True)
                        #p, Q, G1, G2, INT1, INT2 = get_geoms(MS, it, mpoint1, mpoint2, mpoint3)

                        #print(INT1.wkt + ';')
                        #print(INT2.wkt + ';')
                        #print('')

                        #get_unit_regions_inside(MS, mpoint1, mpoint2, mpoint3, region_inside_period)


                        """
                        for e in inside:
                            if isinstance(e, Interval):
                                p, Q, G1, G2, INT1, INT2 = get_geoms(MS, e, mpoint1, mpoint2, mpoint3)
                                print(e.to_string(), 'all')
                                #print(p.wkt + ';')
                                #print(Q.wkt + ';')
                                #print(G1.wkt + ';')
                                #print(G2.wkt + ';')
                                print(INT1.wkt + ';')
                                print(INT2.wkt + ';')
                                print('')
                            else:
                                print(e)

                        print('')
                        """

                        """
                        mr = MovingRegion()
                        for e in inside:
                            if isinstance(e, Interval):
                                ur = MRU()



                                mr.add_unit(ur)
                            else:
                                print(e)

                        print('')
                        """

                        """
                        for e in seg_it:
                            if isinstance(e, Interval):
                                print(e.to_string())
                            else:
                                print(e)

                        print('')
                        #print(interval.to_string())
                        #print('')

                        comp = complement_period(seg_it, interval)

                        for e in comp:
                            if isinstance(e, Interval):
                                print(e.to_string())
                            else:
                                print(e)

                        print('')
                        """

                        """
                        for e in comp:
                            if isinstance(e, Interval):
                                p, Q, G1, G2, INT1, INT2 = get_geoms(MS, e, mpoint1, mpoint2, mpoint3)
                                print(e.to_string(), 'all')
                                #print(p.wkt + ';')
                                #print(Q.wkt + ';')
                                #print(G1.wkt + ';')
                                #print(G2.wkt + ';')
                                print(INT1.wkt + ';')
                                print(INT2.wkt + ';')
                                print('')
                            else:
                                print(e)
                        """

                        sys.exit()

                        """
                        print('')
                        for v in P:
                            it = v[0]
                            np = v[1]

                            if isinstance(it, Interval):
                                print(it.to_string(), np)
                            else:
                                print(it, np)
                        print('')
                        for E in II:
                            for e in E:
                                if isinstance(e, Interval):
                                    print(e.to_string())
                                else:
                                    print(e)
                        print('')
                        for E in II1:
                            for e in E:
                                if isinstance(e, Interval):
                                    print(e.to_string())
                                else:
                                    print(e)
                        print('')
                        for E in II2:
                            for e in E:
                                if isinstance(e, Interval):
                                    print(e.to_string())
                                else:
                                    print(e)
                        print('')
                        """

                        # each e is a unit where the triangle is inside the region.
                        # >>>

                        """
                        inside = intersect_periods(i1, i2)
                        inside = intersect_periods(inside, i3)

                        for e in inside:
                            if isinstance(e, Interval):
                                print(e.to_string())
                            else:
                                print(e)

                        """

                        sys.exit()

                        _IT1 = get_i4(II, MSEG, t)
                        _IT2 = get_i4(II1, MSEG1, t)
                        _IT3 = get_i4(II2, MSEG2, t)

                        coords = []

                        x, y = mpoint1.at(t)
                        coords += [(x, y)]
                        x, y = mpoint2.at(t)
                        coords += [(x, y)]
                        x, y = mpoint3.at(t)
                        coords += [(x, y)]
                        coords += [(coords[0][0], coords[0][1])]
                        geom = Polygon(coords)

                        if len(_IT1) == 0 and len(_IT2) == 0 and len(_IT3) == 0:
                            _geoms += [geom]
                        else:
                            G = []

                            points = get_points_data(i1, i2, i3, mpoint1, mpoint2, mpoint3, t)

                            it = mline0.intersection(geom)

                            if it.is_empty:
                                print('ERR: IT Empty!')
                                sys.exit()
                            elif it.geom_type == 'Polygon' or it.geom_type == 'Point' or it.geom_type == 'LineString':
                                G += [it]
                            elif it.geom_type == 'GeometryCollection':
                                for g in it:
                                    G += [g]
                            elif it.geom_type == 'MultiPolygon':
                                for g in it:
                                    G += [g]
                            elif it.geom_type == 'MultiPoint':
                                for g in it:
                                    G += [g]
                            elif it.geom_type == 'MultiLineString':
                                for g in it:
                                    G += [g]
                            else:
                                print(it.geom_type, 'CC')
                                sys.exit()

                            """
                            print('')
                            for p in points:
                                print(p)
                            print('')
                            for g in G:
                                print(g.wkt)
                            print('')
                            for it in _IT1:
                                print(it)
                                r_seg_id = it[0]
                                u = it[1]
                                #x = it[2]
                                #y = it[3]
                                p = it[2]
                            print('')
                            for it in _IT2:
                                print(it)
                                r_seg_id = it[0]
                                u = it[1]
                                #x = it[2]
                                #y = it[3]
                                p = it[2]
                            print('')
                            for it in _IT3:
                                print(it)
                                r_seg_id = it[0]
                                u = it[1]
                                #x = it[2]
                                #y = it[3]
                                p = it[2]
                            print('')
                            """

                            CORR = []
                            eps = 0.0000001

                            for g in G:
                                coords = g.exterior.coords
                                N = len(coords) - 1
                                i = 0

                                corr = []

                                while i < N:
                                    found = False

                                    x = coords[i][0]
                                    y = coords[i][1]
                                    p = shapely.geometry.Point(x, y)

                                    for point in points:
                                        if point[1].distance(p) < eps:
                                            corr += [(i, 0, point)]
                                            found = True
                                            break

                                    if found:
                                        i += 1
                                        continue

                                    for it in _IT1:
                                        if it[3].distance(p) < eps:
                                            corr += [(i, 1, it)]
                                            found = True
                                            break

                                    if found:
                                        i += 1
                                        continue

                                    for it in _IT2:
                                        if it[3].distance(p) < eps:
                                            corr += [(i, 1, it)]
                                            found = True
                                            break

                                    if found:
                                        i += 1
                                        continue

                                    for it in _IT3:
                                        if it[3].distance(p) < eps:
                                            corr += [(i, 1, it)]
                                            found = True
                                            break

                                    if found:
                                        i += 1
                                        continue

                                    coords2 = mline0.exterior.coords
                                    M = len(coords2) - 1
                                    j = 0

                                    while j < M:
                                        x = coords2[j][0]
                                        y = coords2[j][1]

                                        p1 = shapely.geometry.Point(x, y)

                                        if p1.distance(p) < eps:
                                            corr += [(i, 2, [j, p1])]
                                            found = True
                                            break

                                        j += 1


                                    #print(coords[i], p.wkt)
                                    i += 1

                                CORR += [corr]

                            N = len(G)
                            I = 0

                            print('')

                            t1 = 1100
                            _GEOMS = []

                            while I < N:
                                coords = G[I].exterior.coords
                                corr = CORR[I]

                                M = len(coords) - 1
                                J = 0

                                while J < M:
                                    coord_id = corr[J][0]
                                    v = corr[J][1]
                                    data = corr[J][2]
                                    J += 1

                                    np = None

                                    # point
                                    if v == 0:
                                        pid = data[0]
										
                                        if pid == 0:
                                            x, y = mpoint1.at(t1)
                                        elif pid == 1:
                                            x, y = mpoint2.at(t1)
                                        elif pid == 2:
                                            x, y = mpoint3.at(t1)

                                        np = shapely.geometry.Point(x, y)
                                    # intersection
                                    elif v == 1:
                                        rid = data[0]
                                        pid = data[1]
                                        u = data[2]

                                        if pid == 0:
                                            x, y = get_it_point(pid, u, t1, MSEG)
                                        elif pid == 1:
                                            x, y = get_it_point(pid, u, t1, MSEG1)
                                        elif pid == 2:
                                            x, y = get_it_point(pid, u, t1, MSEG2)

                                        np = shapely.geometry.Point(x, y)
                                    # region boundary
                                    elif v == 2:
                                        pid = data[0]
                                        _coords = mline0.exterior.coords
                                        x = _coords[pid][0]
                                        y = _coords[pid][1]

                                        np = shapely.geometry.Point(x, y)

                                    #print(coords[coord_id], data[len(data)-1].wkt, t)

                                    _GEOMS += [data[len(data)-1].wkt]
                                    _GEOMS += [np]

                                I += 1

                        """
                        for g in it:
                            G += [g]
									
                        for c in CORR:
                            p = c[0]
                            print(c)
                        """

                        sys.exit()

                        # >>>

                        _IDICT = get_i3(II, MSEG, _reg_dict, t)
                        _IDICT1 = get_i3(II1, MSEG1, _reg_dict, t)
                        _IDICT2 = get_i3(II2, MSEG2, _reg_dict, t)

                        points = get_points_data(i1, i2, i3, mpoint1, mpoint2, mpoint3, t)

                        """
                        points = []

                        p_in = False

                        px = 0
                        py = 0

                        p_in = i1[0].contains(t)
                        if p_in:
                            px, py = mpoint1.at(t)

                        points = [(p_in, px, py)]

                        px = 0
                        py = 0

                        p_in = i2[0].contains(t)
                        if p_in:
                            px, py = mpoint2.at(t)

                        points = [(p_in, px, py)]

                        px = 0
                        py = 0

                        p_in = i3[0].contains(t)
                        if p_in:
                            px, py = mpoint3.at(t)

                        points = [(p_in, px, py)]
                        """

                        """
                        for p in points:
                            print(p)

                        sys.exit()
                        """

                        G = []
                        coords = []
                        x, y = mpoint1.at(t)
                        coords += [(x, y)]
                        x, y = mpoint2.at(t)
                        coords += [(x, y)]
                        x, y = mpoint3.at(t)
                        coords += [(x, y)]
                        coords += [(coords[0][0], coords[0][1])]
                        geom1 = Polygon(coords)

                        it = mline0.intersection(geom1)

                        if it.is_empty:
                            print('ERR: IT Empty!')
                            sys.exit()
                        elif it.geom_type == 'Polygon' or it.geom_type == 'Point' or it.geom_type == 'LineString':
                            G += [it]
                        elif it.geom_type == 'GeometryCollection':
                            for g in it:
                                G += [g]
                        elif it.geom_type == 'MultiPolygon':
                            for g in it:
                                G += [g]
                        elif it.geom_type == 'MultiPoint':
                            for g in it:
                                G += [g]
                        elif it.geom_type == 'MultiLineString':
                            for g in it:
                                G += [g]
                        else:
                            print(it.geom_type, 'CC')
                            sys.exit()

                        """
                        print('')

                        for e in G:
                            print(e.wkt + ';', 'AA')

                        print(it.wkt + ';', 'BB')
                        print('')						
                        """

                        _geoms = []

                        if DEBUG:
                            print('')

                            for r in _reg_dict:
                                print(r, _reg_dict[r])

                            print('')

                        if len(_IDICT) == 0 and len(_IDICT1) == 0 and len(_IDICT2) == 0:
                            coords = []
                            x, y = mpoint1.at(t)
                            coords += [(x, y)]
                            x, y = mpoint2.at(t)
                            coords += [(x, y)]
                            x, y = mpoint3.at(t)
                            coords += [(x, y)]
                            coords += [(coords[0][0], coords[0][1])]
                            geom = Polygon(coords)
                            _geoms += [geom]
                        else:
                            for r_seg_id in _IDICT:
                                #print(r_seg_id, _IDICT[r_seg_id], 0)
                                t_s_id = 0
                                v = _IDICT[r_seg_id]
                                if v.v == 0:
                                    geoms += [get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, LETRI, i1, i2, i3, mpoint1, mpoint2, mpoint3, t_s_id, r_seg_id, points,0)]
                                    #geoms += [get_geom(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, LETRI, i1, i2, i3, mpoint1, mpoint2, mpoint3, t_s_id, r_seg_id, 0)]

                            for r_seg_id in _IDICT1:
                                #print(r_seg_id, _IDICT1[r_seg_id], 1)
                                t_s_id = 1
                                v = _IDICT1[r_seg_id]
                                if v.v == 0:
                                    geoms += [get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, LETRI, i1, i2, i3, mpoint1, mpoint2, mpoint3, t_s_id, r_seg_id, points,0)]
                                    #geoms += [get_geom(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, LETRI, i1, i2, i3, mpoint1, mpoint2, mpoint3, t_s_id, r_seg_id, 0)]

                            for r_seg_id in _IDICT2:
                                #print(r_seg_id, _IDICT2[r_seg_id], 2)
                                t_s_id = 2
                                v = _IDICT2[r_seg_id]
                                if v.v == 0:
                                    geoms += [get_geom2(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, LETRI, i1, i2, i3, mpoint1, mpoint2, mpoint3, t_s_id, r_seg_id, points,0)]
                                    #geoms += [get_geom(MS, r_seg_id, _reg_dict, _IDICT, _IDICT1, _IDICT2, t_s_id, v, t, MSEG, MSEG1, MSEG2, LETRI, i1, i2, i3, mpoint1, mpoint2, mpoint3, t_s_id, r_seg_id, 0)]

                            #_geoms = []
                            for g in geoms:
                                if len(g) > 1:
                                    g += [(g[0][0], g[0][1])]
                                    _geoms += [Polygon(g)]
                                else:
                                    _geoms += [shapely.geometry.Point(g[0][0], g[0][1])]

                        #####

                        """
                        print('')

                        for g in _geoms:
                            print(g.wkt + ';')

                        print('')

                        sys.exit()
                        """

                        """
                        _temp = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                        _out = _temp

                        _temp = get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                        _out += _temp

                        _temp = get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                        _out += _temp
                        """

                        #print(GeometryCollection(_out).wkt)
                        print(GeometryCollection(_geoms).wkt)
                        print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    print(mline0.wkt)
                    #print(mline1.wkt)
                    print(GeometryCollection([mline1, mline2, mline3]).wkt)

                    if flag:
                        if out == 1:
                            _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                            _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                            _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                            print(GeometryCollection(_out).wkt)
                        else:
                            print('LINESTRING EMPTY')

                        print(out)
                    else:
                        _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                        _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                        _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                        print(GeometryCollection(_out).wkt)
                        print(1)

                    k += 1

                    eq = True

        if not eq:
            print(mline0.wkt)
            #print(mline1.wkt)
            print(GeometryCollection([mline1, mline2, mline3]).wkt)

            if out == 1:
                _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                print(GeometryCollection(_out).wkt)
            else:
                print('LINESTRING EMPTY')
            print(out)
        else:
            eq = False

#proc_end_exec_time, n_invalid_geoms, n_complex_geoms = samples_for_out7(MS, G, M, I, TRIMS, interval, n_samples, intersections, IP, MPoints, reg_dict, IDICT)
def get_samples_for_out71(MS, G, G1, G2, MSEG, MSEG1, MSEG2, II, II1, II2, ms1, ms2, ms3, i, n_samples, s, i1, i2, i3, mpoint1, mpoint2, mpoint3, reg_dict, IDICT, IDICT1, IDICT2):
    global interval
    global pass_through_control_points
    global print_intersection_information
    global print_solver_execution_time

    P = get_i_period([II, II1, II2])

    region_points_inside_period = get_points_inside_period([i1, i2, i3])

    region_segs_intersection = get_seg_i_period([II, II1, II2])
    region_segs_no_intersection = complement_period(region_segs_intersection, interval)
    region_inside_period = intersection_periods(region_segs_no_intersection, region_points_inside_period)

    gen_geoms = []
    count = 0

    mr = MovingRegion()
    units0 = []
    units1 = []

    for e in P:
        UI = e[0]
        #print(e, UI.to_string())
        #np = v[1]
        if isinstance(UI, Interval):

            t0 = UI.begin()
            t1 = UI.end()

            #print(t0, t1)

            triangle0 = get_triangle_at(mpoint1, mpoint2, mpoint3, t0)
            triangle1 = get_triangle_at(mpoint1, mpoint2, mpoint3, t1)
            triangle2 = get_triangle_at(mpoint1, mpoint2, mpoint3, (t0 + t1) / 2)

            reg0 = get_region_at(MS, t0)
            reg1 = get_region_at(MS, t1)
            reg2 = get_region_at(MS, (t0 + t1) / 2)

            IT01 = get_i5(II, MSEG, t0, t1)
            IT02 = get_i5(II1, MSEG1, t0, t1)
            IT03 = get_i5(II2, MSEG2, t0, t1)

            #C0, G0 = get_corr(reg0, triangle0, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT01, IT02, IT03, t0)

            #C0, G0, ALT, NALT = get_corr2(reg0, triangle0, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT01, IT02, IT03, t0, t1, False, triangle2, reg2)
            C0, G0, ALT, NALT = get_corr3(reg0, triangle0, i1, i2, i3, mpoint1, mpoint2, mpoint3, IT01, IT02, IT03, t0, t1, False, triangle2, reg2)

            counter = 0
            ur = MRU(UI)

            for el in C0:
                coords0, coords1, coords2, MSIDS = get_coords2(el, mpoint1, mpoint2, mpoint3, reg0, reg2, reg1, MSEG, MSEG1, MSEG2, t0, t1)

                DEB = ''
                if NALT[counter] > 1:
                    #print(el)
                    DEB = 'FFFFFFFFFFFFFFFFFFF'

                source_reg = get_geom_from_coords(coords0)
                target_reg = get_geom_from_coords(coords1)
                midlle_obs = get_geom_from_coords(coords2)

                counter += 1
                gen_geoms += [(source_reg, target_reg, UI, reg0, reg1, triangle0, triangle1, midlle_obs, DEB, el)]

                IMS = []
                msu = []

                Z = 1
                E = len(MSIDS)

                #for elem in MSIDS:
                while Z < E:
                    un = []

                    id1 = coords0[MSIDS[Z-1][0]]
                    id2 = coords1[MSIDS[Z-1][1]]
                    id3 = coords2[MSIDS[Z-1][2]]

                    id4 = coords0[MSIDS[Z][0]]
                    id5 = coords1[MSIDS[Z][1]]
                    id6 = coords2[MSIDS[Z][2]]

                    x1 = id1[0]
                    y1 = id1[1]

                    x2 = id2[0]
                    y2 = id2[1]

                    x3 = id3[0]
                    y3 = id3[1]

                    x4 = id4[0]
                    y4 = id4[1]

                    x5 = id5[0]
                    y5 = id5[1]

                    x6 = id6[0]
                    y6 = id6[1]

                    un += [[x1, y1, x2, y2, x3, y3], [x4, y4, x5, y5, x6, y6]]
                    un += [UI.begin(), UI.end()]
                    un = [un, [UI.begin(), UI.end()]]
                    msu += [un]
                    #un += [[x1, y1, x2, y2, x3, y3], [x4, y4, x5, y5, x6, y6]]

                    Z += 1

                for u in msu:
                    IMS += [create_moving_segment2([], pass_through_control_points, [u])]

                # p, q, ms
                ur.add_p(source_reg)
                ur.add_q(reg1.intersection(triangle1))
                ur.add_ms(IMS)

            units0 += [ur]
        else:
            print(UI, 'TODO')

        count += 1
        #if count == 2:
        #    break

    # inside the region
    for e in region_inside_period:
        if isinstance(e, Interval):
            #print(e.to_string(), '--')
            coords0 = []
            coords1 = []
            coords2 = []

            ur = MRU(e)

            t = e.begin()
            x, y = mpoint1.at(t)
            coords0 += [(x, y)]
            x, y = mpoint2.at(t)
            coords0 += [(x, y)]
            x, y = mpoint3.at(t)
            coords0 += [(x, y)]
            coords0 += [(coords0[0][0], coords0[0][1])]

            t = (e.begin() + e.end()) / 2
            x, y = mpoint1.at(t)
            coords1 += [(x, y)]
            x, y = mpoint2.at(t)
            coords1 += [(x, y)]
            x, y = mpoint3.at(t)
            coords1 += [(x, y)]
            coords1 += [(coords1[0][0], coords1[0][1])]

            t = e.end()
            x, y = mpoint1.at(t)
            coords2 += [(x, y)]
            x, y = mpoint2.at(t)
            coords2 += [(x, y)]
            x, y = mpoint3.at(t)
            coords2 += [(x, y)]
            coords2 += [(coords2[0][0], coords2[0][1])]

            msu = []
            E = len(coords2)
            Z = 0
            while Z < E:
                un = []

                id1 = coords0[Z-1]
                id2 = coords1[Z-1]
                id3 = coords2[Z-1]

                id4 = coords0[Z]
                id5 = coords1[Z]
                id6 = coords2[Z]

                x1 = id1[0]
                y1 = id1[1]

                x2 = id2[0]
                y2 = id2[1]

                x3 = id3[0]
                y3 = id3[1]

                x4 = id4[0]
                y4 = id4[1]

                x5 = id5[0]
                y5 = id5[1]

                x6 = id6[0]
                y6 = id6[1]

                un += [[x1, y1, x2, y2, x3, y3], [x4, y4, x5, y5, x6, y6]]
                un += [e.begin(), e.end()]
                un = [un, [e.begin(), e.end()]]
                msu += [un]

                Z += 1

            UMS = []
            for u in msu:
                UMS += [create_moving_segment2([], pass_through_control_points, [u])]

            ur.add_p(Polygon(coords0))
            ur.add_q(Polygon(coords2))
            ur.add_ms(UMS)

            units1 += [ur]
        else:
            print(e, 'all: todo')

    #print(len(mr.get_units()))

    K0 = len(units0)
    K1 = len(units1)

    #print(K0, K1)
    #sys.exit()

    iK0 = 0
    iK1 = 0

    while iK0 < K0 and iK1 < K1:
        u0 = units0[iK0]
        u1 = units1[iK1]

        if u0.i.end() <= u1.i.begin():
            mr.add_unit(u0)
            iK0 += 1
        else:
            mr.add_unit(u1)
            iK1 += 1

    while iK0 < K0:
        u0 = units0[iK0]

        mr.add_unit(u0)
        iK0 += 1

    while iK1 < K1:
        u1 = units1[iK1]

        mr.add_unit(u1)
        iK1 += 1

    n_invalid_geoms = 0
    n_complex_geoms = 0

    # use this for specific testing
    #n_samples = 100
    #get_samples_for_vout2(MS, mr, mpoint1, mpoint2, mpoint3, interval, n_samples)

    proc_end_exec_time = time.time()

    # use this for production
    n_samples = 1500
    n_invalid_geoms, n_complex_geoms = get_samples_for_vout(MS, mr, mpoint1, mpoint2, mpoint3, interval, n_samples)

    return proc_end_exec_time, n_invalid_geoms, n_complex_geoms

def get_samples_for_vout(MS, mr, mpoint1, mpoint2, mpoint3, i, n_samples):
    global TESTING

    n = (n_samples - 1)
    dt = i.y - i.x

    n_invalid_geoms = 0
    n_complex_geoms = 0
    #inv = []
    #counter = 0

    for j in range(0, n_samples):
        t = i.x + dt * (float(j) / n)
        #t01 = (t - i.x) / dt

        reg = get_region_at(MS, t)
        triangle = get_triangle_at(mpoint1, mpoint2, mpoint3, t)
        intersection = mr.at(t)

        if intersection.geom_type == 'Polygon' or intersection.geom_type == 'Point' or intersection.geom_type == 'LineString':
            if not intersection.is_valid:
                n_invalid_geoms += 1
                #inv += [intersection]
                #print(counter, t)
                #sys.exit()

            if not intersection.is_simple:
                n_complex_geoms += 1
        else:
            if not intersection.is_empty:
                for geom in intersection:
                    if not geom.is_valid:
                        n_invalid_geoms += 1
                        #inv += [intersection]

                    if not geom.is_simple:
                        n_complex_geoms += 1

        if TESTING == 0:
            print(reg.wkt)
            print(triangle.wkt)
            print(intersection)
            #print(mr.at(t).wkt)

        #counter += 1

    #print('')
    #for g in inv:
    #    print(g.wkt + ';')
    #print('')

    return n_invalid_geoms, n_complex_geoms

def get_samples_for_vout2(MS, mr, mpoint1, mpoint2, mpoint3, i, n_samples):

    b = 1
    while b < 2:
        u = mr.units[b]

        n = (n_samples - 1)
        dt = u.i.y - u.i.x

        for j in range(0, n_samples):
            t = u.i.x + dt * (float(j) / n)

            reg = get_region_at(MS, t)
            triangle = get_triangle_at(mpoint1, mpoint2, mpoint3, t)

            print(reg.wkt)
            print(triangle.wkt)
            print(u.at(t).wkt)

        b += 1

def get_obs_from_unit(unit, n_samples, op = 0):
    n = (n_samples - 1)
    dt = unit.i.y - unit.i.x

    #t01 = (t - i.x) / dt
    for j in range(0, n_samples):
        t = unit.i.x + dt * (float(j) / n)
        obs = unit.at(t)

        if obs.geom_type == 'Polygon' or obs.geom_type == 'Point' or obs.geom_type == 'LineString':
            if not obs.is_valid:
                if op == 1:
                    g0 = unit.at(unit.i.x)
                    g1 = unit.at((unit.i.y + unit.i.x) / 2)
                    g2 = unit.at(unit.i.y)
                    print(obs.wkt + ';', 'INVALID', t, unit.i.to_string())
                    print(g0.wkt + ';')
                    print(g1.wkt + ';')
                    print(g2.wkt + ';')

            if not obs.is_simple:
                if op == 1:
                    print(obs.wkt + ';', 'NSIMPLE')
        #elif obs.geom_type == 'GeometryCollection' or obs.geom_type == 'MultiPolygon' or obs.geom_type == 'MultiPoint' or obs.geom_type == 'MultiLineString':
        else:
            for geom in obs:
                if not geom.is_valid:
                    if op == 1:
                        print(geom.wkt + ';', 'INVALID')

                if not geom.is_simple:
                    if op == 1:
                        print(geom.wkt + ';', 'NSIMPLE')

        if op == 0:
            print(obs.wkt)
        #print(obs.wkt + ';')
        #print(t)

# Get intersection points.
def get_samples_for_out8(MS, G, G1, G2, MSEG, MSEG1, MSEG2, II, II1, II2, ms1, ms2, ms3, i, n_samples, s, i1, i2, i3, mpoint1, mpoint2, mpoint3, reg_dict, IDICT, IDICT1, IDICT2):
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
    i1_len = len(i1)
    i2_len = len(i2)
    i3_len = len(i3)
    i1_idx = 0
    i2_idx = 0
    i3_idx = 0

    LENMS = len(MS)
    LETRI = 3

    """
    print_i_periods(II)
    print_i_periods(II1)
    print_i_periods(II2)
    sys.exit()
    """

    for j in range(0, n_samples):
        t = i.x + dt * (float(j) / n)
        t01 = (t - i.x) / dt
        out = 0
        flag = False

        #mpoint1_in = False
        #mpoint2_in = False

        #mpoint1_pos = None
        #mpoint2_pos = None

        if J < N and t >= T[J]:
            t = T[J]
            t01 = (t - i.x) / dt
            out = K[J]
            J += 1
            flag = True

        mline0 = get_region_at(MS, t)
        mline1 = ms1.obj_at(t)
        mline2 = ms2.obj_at(t)
        mline3 = ms3.obj_at(t)

        #print(GeometryCollection([mline1, mline2, mline3]).wkt)

        coll = []
        geoms = []

        if len(s) > 0 and k < len(s):
            if isinstance(s[k], Interval):
                if s[k].contains(t):
                    print(mline0.wkt)
                    #print(mline1.wkt)
                    print(GeometryCollection([mline1, mline2, mline3]).wkt)

                    if flag:
                        if out == 1:
                            _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                            _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                            _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)

                            print(GeometryCollection(_out).wkt)
                        else:
                            print('LINESTRING EMPTY')

                        print(out)
                    else:
                        _temp = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                        _out = _temp

                        _temp = get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                        _out += _temp

                        _temp = get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                        _out += _temp

                        print(GeometryCollection(_out).wkt)
                        print(1)

                    eq = True
                
                if s[k].y <= t:
                    k += 1
            else:
                if s[k] <= t:
                    print(mline0.wkt)
                    #print(mline1.wkt)
                    print(GeometryCollection([mline1, mline2, mline3]).wkt)

                    if flag:
                        if out == 1:
                            _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                            _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                            _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                            print(GeometryCollection(_out).wkt)
                        else:
                            print('LINESTRING EMPTY')

                        print(out)
                    else:
                        _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                        _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                        _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                        print(GeometryCollection(_out).wkt)
                        print(1)

                    k += 1

                    eq = True

        if not eq:
            print(mline0.wkt)
            #print(mline1.wkt)
            print(GeometryCollection([mline1, mline2, mline3]).wkt)

            if out == 1:
                _out = get_seg(II, MSEG, t, i1_idx, i1_len, mpoint1, i1, i2_idx, i2_len, mpoint2, i2)
                _out += get_seg(II1, MSEG1, t, i2_idx, i2_len, mpoint2, i2, i3_idx, i3_len, mpoint3, i3, 2)
                _out += get_seg(II2, MSEG2, t, i3_idx, i3_len, mpoint3, i3, i1_idx, i1_len, mpoint1, i1, 3)
                print(GeometryCollection(_out).wkt)
            else:
                print('LINESTRING EMPTY')
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
def get_intersection_information(intersection_instants, msegs0, msegs1, op):
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
    elif op == Operation.Overlaps.value:
        info = "Overlaps: "
    elif op == Operation.CoveredBy.value:
        info = "CoveredBy: "
    elif op == Operation.Covers.value:
        info = "Covers: "
    elif op == Operation.Equals.value:
        info = "Equals: "
    #elif op == STOperation.Intersection.value:
    #    info = "Intersection: "

    for t in intersection_instants:
        if add_comma:
            info += ", "
        else:
            add_comma = True

        if isinstance(t, Interval):
            #P0x, P0y = mp.at(t.x)
            #P1x, P1y = mp.at(t.y)

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
            #Px, Py = mp.at(t)
			
            info += 't: ' + format(t, precision)
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

def get_solutions_quad(a0, a1, a2, it):
    global eps

    s_exec_time = time.time()
    if a2 == 0:
        #print(a2, '--')
        return 0, []

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

        if im(r1) == 0:
            r += [re(r1)]
    else:
        #print(a2)
        r1 = (-a1 - cmath.sqrt(det)) / (2*a2)
        r2 = (-a1 + cmath.sqrt(det)) / (2*a2)

        if im(r1) == 0:
            r += [re(r1)]

        if im(r2) == 0:
            r += [re(r2)]

        """
        if r1 < r2:
            r += [r1]
            r += [r2]
        else:
            r += [r2]
            r += [r1]
        """

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

                # temp
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

def get_mr_mp_intersections(MS, mp, initial_state, final_state, op = 1):

    msegs = []

    for ms in MS:
        msegs += [create_moving_segment([ms], pass_through_control_points)]

    intersections = None

    for ms in msegs:    
        intersections = get_intersections_3(ms, mp, interval, intersections)

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
            """

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
                    I = Interval(intersection.x, intersection.y, False, False)
                    comp += [intersection.x, intersection.y]
                else:
                    comp += [intersection]

        intersections = comp
    """
    elif op == STOperation.Intersection.value:
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

    get_samples_for_out(msegs, mp, interval, n_samples, intersections)
    #get_samples_for_viz_2(msegs, mp, interval, n_samples, intersections)

    if print_intersection_information:
        print(get_intersection_information(intersections, msegs, mp, op))

    if print_solver_execution_time:
        print("Exec. Time: "+ format(solver_exec_time, precision) + "sec, NE: " + str(solver_exec_times))

    #if op == STOperation.Intersection.value:
    #    print(intersection_geom.wkt)

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

def get_moving_segs_from_observations2(p_wkt, q_wkt, i_wkt, t0, t1):
    global err_msg
    global err_code
	
    p = loads(p_wkt)
    q = loads(q_wkt)

    # get moving segments from p to q

    #msegs = get_msegs_simple_polygons_with_corr(p, q)

    g = loads(i_wkt)

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

def print_interpolation(p_wkt, q_wkt, n_samples, t0, t1):

    p = loads(p_wkt)
    q = loads(q_wkt)

    # get moving segments from p to q

    msegs = get_msegs_simple_polygons_with_corr(p, q)
	
    n = (n_samples - 1)
    dt = t1 - t0

    for j in range(0, n_samples):
        #t = t0 + dt * (float(j) / n)
        t = (float(j)) / n

        k = 0
        coords = []

        for mseg in msegs:
            xi, yi, xf, yf = mseg.at2(t)

            if k == 0:
                coords += [[xi, yi]]
                k = 1

            coords += [[xf, yf]]               

        g = Polygon(coords)

        if not g.is_valid:
            #err_msg = 'get_moving_segs_from_observations() : Invalid Observation.'
            return None
                        
        if not g.is_simple:
            #err_msg = 'get_moving_segs_from_observations() : Non-simple Observation.'
            return None

        print(g.wkt)
        print(Polygon().wkt)
        print(0)

    if print_intersection_information:
        print('NI: 0:')

    if print_solver_execution_time:
        print('Exec. Time: 0sec, NE: 0')

#-------------------------------------------------------------------
# Do work.
#-------------------------------------------------------------------
"""
coeff = [3.2, 2, 1]
r = np.roots(coeff)
print(r)
"""

"""
coeff = [1, 0, 0]
r = np.roots(coeff)
print(r)
"""

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

def print_roots(roots):
    for root in roots:
        if isinstance(root, Interval):
            print(root.to_string())
        else:
            print(root)

def msegs_intersect_at_t(msu1, msu2, t):
    Ax, Ay, Bx, By = msu1.at(t)
    Cx, Cy, Dx, Dy = msu2.at(t)

    d1 = dir(Ax, Ay, Bx, By, Cx, Cy)
    d2 = dir(Ax, Ay, Bx, By, Dx, Dy)
    d3 = dir(Cx, Cy, Dx, Dy, Ax, Ay)
    d4 = dir(Cx, Cy, Dx, Dy, Bx, By)

    return (d1 * d2) < 0 and (d3 * d4) < 0

def msegs_intersect_at_midpoint(msu1, msu2, t1, t2):
    t = (t1 + t2) / 2

    Ax, Ay, Bx, By = msu1.at(t)
    Cx, Cy, Dx, Dy = msu2.at(t)

    d1 = dir(Ax, Ay, Bx, By, Cx, Cy)
    d2 = dir(Ax, Ay, Bx, By, Dx, Dy)
    d3 = dir(Cx, Cy, Dx, Dy, Ax, Ay)
    d4 = dir(Cx, Cy, Dx, Dy, Bx, By)

    return (d1 * d2) < 0 and (d3 * d4) < 0

def get_int(msu1, msu2, it0, r1, msegs_intersect_at_t0):                      
    r = []

    # msegs intersect.
    if msegs_intersect_at_t0:
        if it0.x == r1[0]:
            if msegs_intersect_at_midpoint(msu1, msu2, r1[0], it0.y):
                I = Interval(r1[0], it0.y, True, True)
                r = [I]
            else:
                r = [r1[0]]
        else:
            I = Interval(it0.x, r1[0], True, True)
            r = [I]
    else:
        # msegs intersect.
        if r1[0] == it0.y:
            r = [r1[0]]
        elif msegs_intersect_at_midpoint(msu1, msu2, r1[0], it0.y):
            I = Interval(r1[0], it0.y, True, True)
            r = [I]
        # 2.2 collinear.
        #elif (d1 * d2) == 0 or (d3 * d4) == 0:
		#   ...
        # 2.3 touch.
        else:
            r = [r1[0]]

    return r

def quad_roots(a, b, c, w, v, y, s, d, z, p, it):
    a0 = (a*d**2*p**2 + 2*a*d*p**2*s + a*p**2*s**2 - 2*b*d*p**2*s - 2*b*p**2*s**2 + c*p**2*s**2 - d**2*p**2*w + 2*d**2*p*v*z - 2*d**2*p*w*z + 2*d**2*v*z**2 - d**2*w*z**2 - d**2*y*z**2) / (d**2*p**2)
    a1 = (-2*a*d*p**2 - 2*a*p**2*s + 2*b*d*p**2 + 4*b*p**2*s - 2*c*p**2*s - 2*d**2*p*v + 2*d**2*p*w - 4*d**2*v*z + 2*d**2*w*z + 2*d**2*y*z) / (d**2*p**2)
    a2 = (+a*p**2 - 2*b*p**2 + c*p**2 + 2*d**2*v - d**2*w - d**2*y) / (d**2*p**2)
    #print(a0, a1, a2)
    exec_time, r = get_solutions_quad(a0, a1, a2, it)
    return exec_time, r

def intersection(lst1, lst2):
    temp = set(lst2)
    lst3 = [value for value in lst1 if value in temp]
    return lst3

def intersection2(lst1, lst2):
    global eps
    lst3 = []

    for v in lst1:
        for e in lst2:
            d = v - e
            if d < 0:
                d = d * -1

            if d < eps:
                lst3 += [v]
    
    return lst3

def get_msegs_equals(ms1, ms2, i, prev_it = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon

    s_exec_time = time.time()

    s = []

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

                    r = []
                    done = False

                    # Cx - Bx
                    #f = Cx - Bx
                    #a0 = (-msu_dt**2*mpu_dt*c1_cp0_x + msu_dt**2*mpu_dt*x0 - msu_dt**2*mpu_t0*dx + 2*msu_dt*mpu_dt*c1_cp1_x*msu_t0 - 2*msu_dt*mpu_dt*c1_cp0_x*msu_t0 - c1_cp2_x*mpu_dt*msu_t0**2 + 2*mpu_dt*c1_cp1_x*msu_t0**2 - mpu_dt*c1_cp0_x*msu_t0**2) / (msu_dt**2*mpu_dt)
                    #a1 = (+msu_dt**2*dx - 2*msu_dt*mpu_dt*c1_cp1_x + 2*msu_dt*mpu_dt*c1_cp0_x + 2*c1_cp2_x*mpu_dt*msu_t0 - 4*mpu_dt*c1_cp1_x*msu_t0 + 2*mpu_dt*c1_cp0_x*msu_t0) / (msu_dt**2*mpu_dt)
                    #a2 = (-c1_cp2_x*mpu_dt + 2*mpu_dt*c1_cp1_x - mpu_dt*c1_cp0_x) / (msu_dt**2*mpu_dt)

                    #exec_time, r = get_solutions(f, t, it0)
                    #f = Ax - Cx
                    exec_time, r = quad_roots(c0_cp0_x, c0_cp1_x, c0_cp2_x, c2_cp0_x, c2_cp1_x, c2_cp2_x, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it0)
                    #print(r)
                    if r != []:
                        #print('111')
                        #f = Ay - Cy
                        exec_time1, r1 = quad_roots(c0_cp0_y, c0_cp1_y, c0_cp2_y, c2_cp0_y, c2_cp1_y, c2_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it0)
                        #print(r, r1)
                        """
                        for v in r:
                            for e in r1:
                                print(v - e)
                                if e == v:
                                    print(e, 'eq')
                                    break
                        """
                        #r = intersection(r, r1) 
                        r = intersection2(r, r1) 
                        #print(r)
                        exec_time += exec_time1

                    #print('>>>')
                    if r == []:
                        #print('000')
                        #print('2')
                        #f = Ax - Dx
                        exec_time1, r = quad_roots(c0_cp0_x, c0_cp1_x, c0_cp2_x, c3_cp0_x, c3_cp1_x, c3_cp2_x, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it0)
                        exec_time += exec_time1
                        #print(r)

                        if r != []:
                            #f = Ay - Dy
                            exec_time1, r1 = quad_roots(c0_cp0_y, c0_cp1_y, c0_cp2_y, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it0)
                            #print(r1)
                            #r = intersection(r, r1)
                            r = intersection2(r, r1) 
                            exec_time += exec_time1

                    #f = Bx - Dx
                    #f = By - Dy

                    #f = Ax - Dx
                    #f = Ay - Dy
                    #f = Bx - Cx
                    #f = By - Cy

                    #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                    #exec_time, r1 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                    #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                    #exec_time, r2 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                    #f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx)))
                    #exec_time, r3 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                    #f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                    #exec_time, r4 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                    solver_exec_times += 2

                    #r1 = get_valid_roots(msu1, msu2, r1, 1)
                    #r2 = get_valid_roots(msu1, msu2, r2, 2)
                    #r3 = get_valid_roots(msu1, msu2, r3, 3)
                    #r4 = get_valid_roots(msu1, msu2, r4, 4)
                    #print(r, '--')
                    s += r

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

    # sort intersections.
	
    if prev_it != None and len(prev_it) > 0 and len(s) > 0:
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

                #print(x1.to_string(), x2.to_string())

                if ix1 < ix2:
                    _sorted += [x1]
                    i += 1
                elif ix3 < ix0:
                    _sorted += [x2]
                    j += 1
                # overlap
                else:
                    _sorted += [Interval(min(ix0, ix2), max(ix1, ix3), True, True)]
                    i += 1
                    j += 1
                #sys.exit()
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

                #print(x1, ix0, ix1, x2, isinstance(x2, Interval))

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

        last = _sorted[len(_sorted)-1]

        while i < n:
            #_sorted += [prev_it[i]]
            if isinstance(last, Interval) and isinstance(prev_it[i], Interval):
                if last.intersects(prev_it[i]):
                    ix0 = last.begin()
                    ix1 = last.end()
                    ix2 = prev_it[i].begin()
                    ix3 = prev_it[i].end()
                    #print(_sorted[len(_sorted)-1])
                    I = Interval(min(ix0, ix2), max(ix1, ix3), True, True)
                    _sorted[len(_sorted)-1] = I
                    #print(_sorted[len(_sorted)-1])
                else:
                    _sorted += [prev_it[i]]
            elif isinstance(last, Interval):
                if prev_it[i] > last.y:
                    _sorted += [prev_it[i]]
            else:
                _sorted += [prev_it[i]]

            last = _sorted[len(_sorted)-1]
            i += 1

        while j < m:
            if isinstance(last, Interval) and isinstance(s[j], Interval):
                if last.intersects(s[j]):
                    ix0 = last.begin()
                    ix1 = last.end()
                    ix2 = s[j].begin()
                    ix3 = s[j].end()
                    #print(_sorted[len(_sorted)-1])
                    I = Interval(min(ix0, ix2), max(ix1, ix3), True, True)
                    _sorted[len(_sorted)-1] = I
                    #print(_sorted[len(_sorted)-1])
                else:
                    _sorted += [s[j]]
            elif isinstance(last, Interval):
                if s[j] > last.y:
                    _sorted += [s[j]]
            else:
                _sorted += [s[j]]

            last = _sorted[len(_sorted)-1]
            j += 1

        s = _sorted
    elif prev_it != None and len(prev_it) > 0 and len(s) == 0:
        s = prev_it

    e_exec_time = time.time()
    solver_exec_time += e_exec_time - s_exec_time

    return s

def get_msegs_intersections(ms1, ms2, i, prev_it = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon

    s_exec_time = time.time()

    s = []

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

                    r = []

                    done = False

                    if col == 0:

                        msegs_intersect_at_t0 = msegs_intersect_at_t(msu1, msu2, it0.x)
                        #print(initial_msegs_state)

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

                        #print(r1, r2, r3, r4)

                        solver_exec_times += 4

                        r1 = get_valid_roots(msu1, msu2, r1, 1)
                        r2 = get_valid_roots(msu1, msu2, r2, 2)
                        r3 = get_valid_roots(msu1, msu2, r3, 3)
                        r4 = get_valid_roots(msu1, msu2, r4, 4)

                        if len(r1) == 0 and len(r2) == 0 and len(r3) == 0 and len(r4) == 0:
                            if msu1.c0.intervals[idx1].y == msu2.c0.intervals[idx2].y:
                                idx1 += 1
                                idx2 += 1
                            elif msu1.c0.intervals[idx1].y < msu2.c0.intervals[idx2].y:
                                idx1 += 1
                            else:
                                idx2 += 1

                            continue

                        #print(r1, r2, r3, r4)
                        #sys.exit()

                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                        #exec_time, r1 = get_solutions(f, t, it)
                        #exec_time, r1 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        #exec_time, r2 = get_solutions(f, t, it)
                        #exec_time, r2 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #print(r1, r2)
                        #print(r1, r2, r3, r4)

                        #r = []

                        # 1. both endpoints of one of the segments intersect the other segment
                        if len(r1) == 1 and len(r2) == 1 and len(r3) == 0 and len(r4) == 0:
                            # 1.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r1[0], r2[0]):
                                I = Interval(min(r1[0], r2[0]), max(r1[0], r2[0]), True, True)
                                r = [I]
                            # 1.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 1.3 touch.
                            else:
                                r = [r1[0], r2[0]]
                                r.sort()

                            """
                            # 1. touch or intersect?

                            t = (r1[0] + r2[0]) / 2

                            Ax, Ay, Bx, By = msu1.at(t)
                            Cx, Cy, Dx, Dy = msu2.at(t)

                            d1 = dir(Ax, Ay, Bx, By, Cx, Cy)
                            d2 = dir(Ax, Ay, Bx, By, Dx, Dy)
                            d3 = dir(Cx, Cy, Dx, Dy, Ax, Ay)
                            d4 = dir(Cx, Cy, Dx, Dy, Bx, By)

                            # 1.1 intersect.
                            if (d1 * d2) < 0 and (d3 * d4) < 0:
                                I = Interval(min(r1[0], r2[0]), max(r1[0], r2[0]), True, True)
                                r = [I]
                            # 1.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 1.3 touch.
                            else:
                                r = [r1[0], r2[0]]
                                r.sort()
                            """
                            #print_roots(r)
                        # 1. both endpoints of one of the segments intersect the other segment
                        elif len(r1) == 0 and len(r2) == 0 and len(r3) == 1 and len(r4) == 1:
                            # 1.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r3[0], r4[0]):
                                I = Interval(min(r3[0], r4[0]), max(r3[0], r4[0]), True, True)
                                r = [I]
                            # 1.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 1.3 touch.
                            else:
                                r = [r3[0], r4[0]]
                                r.sort()

                            """
                            t = (r3[0] + r4[0]) / 2

                            Ax, Ay, Bx, By = msu1.at(t)
                            Cx, Cy, Dx, Dy = msu2.at(t)

                            d1 = dir(Ax, Ay, Bx, By, Cx, Cy)
                            d2 = dir(Ax, Ay, Bx, By, Dx, Dy)
                            d3 = dir(Cx, Cy, Dx, Dy, Ax, Ay)
                            d4 = dir(Cx, Cy, Dx, Dy, Bx, By)

                            if (d1 * d2) < 0 and (d3 * d4) < 0:
                                I = Interval(min(r3[0], r4[0]), max(r3[0], r4[0]), True, True)
                                r = [I]
                            else:
                                r = [r3[0], r4[0]]
                                r.sort()
                            """
                        # 2. an endpoint of one of the segments intersects the other segment
                        elif len(r1) == 1 and len(r2) == 0 and len(r3) == 0 and len(r4) == 0:
                            r = get_int(msu1, msu2, it0, r1, msegs_intersect_at_t0)

                            """
                            # 2.1 msegs intersect.
                            if msegs_intersect_at_t0:
                                if it0.x == r1[0]:
                                    if msegs_intersect_at_midpoint(msu1, msu2, r1[0], it0.y):
                                        I = Interval(min(r1[0], it0.y), max(r1[0], it0.y), True, True)
                                        r = [I]
                                    else:
                                        r = [r1[0]]
                                else:
                                    I = Interval(it0.x, r1[0], True, True)
                                    r = [I]
                            else:
                                if msegs_intersect_at_midpoint(msu1, msu2, r1[0], it0.y):
                                    I = Interval(min(r1[0], it0.y), max(r1[0], it0.y), True, True)
                                    r = [I]
                                # 2.2 collinear.
                                #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							    #   ...
                                # 2.3 touch.
                                else:
                                    r = [r1[0], it0.y]
                                    r.sort()
                            """
                        # 2. an endpoint of one of the segments intersects the other segment
                        elif len(r1) == 0 and len(r2) == 1 and len(r3) == 0 and len(r4) == 0:
                            r = get_int(msu1, msu2, it0, r2, msegs_intersect_at_t0)

                            """
                            # 2.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r2[0], it0.y):
                                I = Interval(min(r2[0], it0.y), max(r2[0], it0.y), True, True)
                                r = [I]
                            # 2.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 2.3 touch.
                            else:
                                r = [r2[0], it0.y]
                                r.sort()
                            """
                        # 2. an endpoint of one of the segments intersects the other segment
                        elif len(r1) == 0 and len(r2) == 0 and len(r3) == 1 and len(r4) == 0:
                            r = get_int(msu1, msu2, it0, r3, msegs_intersect_at_t0)

                            """
                            # 2.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r3[0], it0.y):
                                I = Interval(min(r3[0], it0.y), max(r3[0], it0.y), True, True)
                                r = [I]
                            # 2.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 2.3 touch.
                            else:
                                r = [r3[0], it0.y]
                                r.sort()
                            """
                        # 2. an endpoint of one of the segments intersects the other segment
                        elif len(r1) == 0 and len(r2) == 0 and len(r3) == 0 and len(r4) == 1:
                            r = get_int(msu1, msu2, it0, r4, msegs_intersect_at_t0)

                            """
                            # 2.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r4[0], it0.y):
                                I = Interval(min(r4[0], it0.y), max(r4[0], it0.y), True, True)
                                r = [I]
                            # 2.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 2.3 touch.
                            else:
                                r = [r4[0], it0.y]
                                r.sort()
                            #print_roots(r)
                            """
                        # 3. an endpoint of both segments intersects the other segment
                        elif len(r1) == 1 and len(r2) == 0 and len(r3) == 1 and len(r4) == 0:
                            # 3.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r1[0], r3[0]):
                                I = Interval(min(r1[0], r3[0]), max(r1[0], r3[0]), True, True)
                                r = [I]
                            # 3.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 3.3 touch.
                            else:
                                r = [r1[0], r3[0]]
                                r.sort()
                        # 3. an endpoint of both segments intersects the other segment
                        elif len(r1) == 1 and len(r2) == 0 and len(r3) == 0 and len(r4) == 1:
                            # 3.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r1[0], r4[0]):
                                I = Interval(min(r1[0], r4[0]), max(r1[0], r4[0]), True, True)
                                r = [I]
                            # 3.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 3.3 touch.
                            else:
                                r = [r1[0], r4[0]]
                                r.sort()
                        # 3. an endpoint of both segments intersects the other segment
                        elif len(r1) == 0 and len(r2) == 1 and len(r3) == 1 and len(r4) == 0:
                            # 3.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r2[0], r3[0]):
                                I = Interval(min(r2[0], r3[0]), max(r2[0], r3[0]), True, True)
                                r = [I]
                            # 3.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 3.3 touch.
                            else:
                                r = [r2[0], r3[0]]
                                r.sort()
                        # 3. an endpoint of both segments intersects the other segment
                        elif len(r1) == 0 and len(r2) == 1 and len(r3) == 0 and len(r4) == 1:
                            # 3.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r2[0], r4[0]):
                                I = Interval(min(r2[0], r4[0]), max(r2[0], r4[0]), True, True)
                                r = [I]
                            # 3.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 3.3 touch.
                            else:
                                r = [r2[0], r4[0]]
                                r.sort()
                        # 4. an endpoint of a segment intersects the other segment twice.
                        elif len(r1) == 2 and len(r2) == 0 and len(r3) == 0 and len(r4) == 0:
                            # 4.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r1[0], r1[1]):
                                I = Interval(min(r1[0], r1[1]), max(r1[0], r1[1]), True, True)
                                r = [I]
                            # 4.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 4.3 touch.
                            else:
                                r = [r1[0], r1[1]]
                                r.sort()
                            #print_roots(r)
                        # 4. an endpoint of a segment intersects the other segment twice.
                        elif len(r1) == 0 and len(r2) == 2 and len(r3) == 0 and len(r4) == 0:
                            # 4.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r2[0], r2[1]):
                                I = Interval(min(r2[0], r2[1]), max(r2[0], r2[1]), True, True)
                                r = [I]
                            # 4.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 4.3 touch.
                            else:
                                r = [r2[0], r2[1]]
                                r.sort()
                        # 4. an endpoint of a segment intersects the other segment twice.
                        elif len(r1) == 0 and len(r2) == 0 and len(r3) == 2 and len(r4) == 0:
                            # 4.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r3[0], r3[1]):
                                I = Interval(min(r3[0], r3[1]), max(r3[0], r3[1]), True, True)
                                r = [I]
                            # 4.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 4.3 touch.
                            else:
                                r = [r3[0], r3[1]]
                                r.sort()
                        # 4. an endpoint of a segment intersects the other segment twice.
                        elif len(r1) == 0 and len(r2) == 0 and len(r3) == 0 and len(r4) == 2:
                            # 4.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r4[0], r4[1]):
                                I = Interval(min(r4[0], r4[1]), max(r4[0], r4[1]), True, True)
                                r = [I]
                            # 4.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 4.3 touch.
                            else:
                                r = [r4[0], r4[1]]
                                r.sort()
                        # 5. .
                        """
                        elif len(r1) == 0 and len(r2) == 1:
                            pass
                        # 5. disjoint.
                        #elif len(r1) == 0 and len(r2) == 0 and len(r3) == 0 and len(r4) == 0:
                        #   ...
                        """

                        #sys.exit()
                        #r = []

                        """
						([], [1924.16039889982])
						([], [1735.84203882648])						
                        """

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
                        """

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

                    # need to sort the intersections in the future, when working with 1+ units.
                    """
                    for I in r:
                        if isinstance(I, Interval):
                            print(I.to_string())
                        else:
                            print(I)
                    """
                    # temp
                    s += r

                    """
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
                    """

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

    # sort intersections.
	
    if prev_it != None and len(prev_it) > 0 and len(s) > 0:
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

                #print(x1.to_string(), x2.to_string())

                if ix1 < ix2:
                    _sorted += [x1]
                    i += 1
                elif ix3 < ix0:
                    _sorted += [x2]
                    j += 1
                # overlap
                else:
                    _sorted += [Interval(min(ix0, ix2), max(ix1, ix3), True, True)]
                    i += 1
                    j += 1
                #sys.exit()
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

                #print(x1, ix0, ix1, x2, isinstance(x2, Interval))

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

        last = _sorted[len(_sorted)-1]

        while i < n:
            #_sorted += [prev_it[i]]
            if isinstance(last, Interval) and isinstance(prev_it[i], Interval):
                if last.intersects(prev_it[i]):
                    ix0 = last.begin()
                    ix1 = last.end()
                    ix2 = prev_it[i].begin()
                    ix3 = prev_it[i].end()
                    #print(_sorted[len(_sorted)-1])
                    I = Interval(min(ix0, ix2), max(ix1, ix3), True, True)
                    _sorted[len(_sorted)-1] = I
                    #print(_sorted[len(_sorted)-1])
                else:
                    _sorted += [prev_it[i]]
            elif isinstance(last, Interval):
                if prev_it[i] > last.y:
                    _sorted += [prev_it[i]]
            else:
                _sorted += [prev_it[i]]

            last = _sorted[len(_sorted)-1]
            i += 1

        while j < m:
            if isinstance(last, Interval) and isinstance(s[j], Interval):
                if last.intersects(s[j]):
                    ix0 = last.begin()
                    ix1 = last.end()
                    ix2 = s[j].begin()
                    ix3 = s[j].end()
                    #print(_sorted[len(_sorted)-1])
                    I = Interval(min(ix0, ix2), max(ix1, ix3), True, True)
                    _sorted[len(_sorted)-1] = I
                    #print(_sorted[len(_sorted)-1])
                else:
                    _sorted += [s[j]]
            elif isinstance(last, Interval):
                if s[j] > last.y:
                    _sorted += [s[j]]
            else:
                _sorted += [s[j]]

            last = _sorted[len(_sorted)-1]
            j += 1

        s = _sorted
    elif prev_it != None and len(prev_it) > 0 and len(s) == 0:
        s = prev_it

    """
    print('')
    for I in s:
        if isinstance(I, Interval):
            print(I.to_string())
        else:
            print(I)
    """

    e_exec_time = time.time()
    solver_exec_time += e_exec_time - s_exec_time

    return s

def get_msegs_intersections2(ms1, ms2, i, prev_it = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon

    s_exec_time = time.time()

    s = []

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

                    r = []

                    done = False

                    if col == 0:

                        msegs_intersect_at_t0 = msegs_intersect_at_t(msu1, msu2, it0.x)
                        #print(initial_msegs_state)

                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                        exec_time, r1 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        exec_time, r2 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx)))
                        exec_time, r3 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r4 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #print(r1, r2, r3, r4)

                        solver_exec_times += 4

                        r1 = get_valid_roots(msu1, msu2, r1, 1)
                        r2 = get_valid_roots(msu1, msu2, r2, 2)
                        r3 = get_valid_roots(msu1, msu2, r3, 3)
                        r4 = get_valid_roots(msu1, msu2, r4, 4)

                        #print(len(r1), len(r2), len(r3), len(r4))

                        if len(r1) == 0 and len(r2) == 0 and len(r3) == 0 and len(r4) == 0:
                            if msu1.c0.intervals[idx1].y == msu2.c0.intervals[idx2].y:
                                idx1 += 1
                                idx2 += 1
                            elif msu1.c0.intervals[idx1].y < msu2.c0.intervals[idx2].y:
                                idx1 += 1
                            else:
                                idx2 += 1

                            continue

                        # 1. both endpoints of one of the segments intersect the other segment
                        if len(r1) == 1 and len(r2) == 1 and len(r3) == 0 and len(r4) == 0:
                            # 1.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r1[0], r2[0]):
                                I = Interval(min(r1[0], r2[0]), max(r1[0], r2[0]), True, True)
                                r = [I]
                            # 1.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 1.3 touch.
                            else:
                                r = [r1[0], r2[0]]
                                r.sort()
                            #print_roots(r)
                        # 1. both endpoints of one of the segments intersect the other segment
                        elif len(r1) == 0 and len(r2) == 0 and len(r3) == 1 and len(r4) == 1:
                            # 1.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r3[0], r4[0]):
                                I = Interval(min(r3[0], r4[0]), max(r3[0], r4[0]), True, True)
                                r = [I]
                            # 1.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 1.3 touch.
                            else:
                                r = [r3[0], r4[0]]
                                r.sort()
                        # 2. an endpoint of one of the segments intersects the other segment
                        elif len(r1) == 1 and len(r2) == 0 and len(r3) == 0 and len(r4) == 0:
                            r = get_int(msu1, msu2, it0, r1, msegs_intersect_at_t0)
                        # 2. an endpoint of one of the segments intersects the other segment
                        elif len(r1) == 0 and len(r2) == 1 and len(r3) == 0 and len(r4) == 0:
                            r = get_int(msu1, msu2, it0, r2, msegs_intersect_at_t0)
                        # 2. an endpoint of one of the segments intersects the other segment
                        elif len(r1) == 0 and len(r2) == 0 and len(r3) == 1 and len(r4) == 0:
                            r = get_int(msu1, msu2, it0, r3, msegs_intersect_at_t0)
                        # 2. an endpoint of one of the segments intersects the other segment
                        elif len(r1) == 0 and len(r2) == 0 and len(r3) == 0 and len(r4) == 1:
                            r = get_int(msu1, msu2, it0, r4, msegs_intersect_at_t0)
                        # 3. an endpoint of both segments intersects the other segment
                        elif len(r1) == 1 and len(r2) == 0 and len(r3) == 1 and len(r4) == 0:
                            # 3.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r1[0], r3[0]):
                                I = Interval(min(r1[0], r3[0]), max(r1[0], r3[0]), True, True)
                                r = [I]
                            # 3.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 3.3 touch.
                            else:
                                r = [r1[0], r3[0]]
                                r.sort()
                        # 3. an endpoint of both segments intersects the other segment
                        elif len(r1) == 1 and len(r2) == 0 and len(r3) == 0 and len(r4) == 1:
                            # 3.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r1[0], r4[0]):
                                I = Interval(min(r1[0], r4[0]), max(r1[0], r4[0]), True, True)
                                r = [I]
                            # 3.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 3.3 touch.
                            else:
                                r = [r1[0], r4[0]]
                                r.sort()
                        # 3. an endpoint of both segments intersects the other segment
                        elif len(r1) == 0 and len(r2) == 1 and len(r3) == 1 and len(r4) == 0:
                            # 3.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r2[0], r3[0]):
                                I = Interval(min(r2[0], r3[0]), max(r2[0], r3[0]), True, True)
                                r = [I]
                            # 3.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 3.3 touch.
                            else:
                                r = [r2[0], r3[0]]
                                r.sort()
                        # 3. an endpoint of both segments intersects the other segment
                        elif len(r1) == 0 and len(r2) == 1 and len(r3) == 0 and len(r4) == 1:
                            # 3.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r2[0], r4[0]):
                                I = Interval(min(r2[0], r4[0]), max(r2[0], r4[0]), True, True)
                                r = [I]
                            # 3.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 3.3 touch.
                            else:
                                r = [r2[0], r4[0]]
                                r.sort()
                        # 4. an endpoint of a segment intersects the other segment twice.
                        elif len(r1) == 2 and len(r2) == 0 and len(r3) == 0 and len(r4) == 0:
                            # 4.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r1[0], r1[1]):
                                I = Interval(min(r1[0], r1[1]), max(r1[0], r1[1]), True, True)
                                r = [I]
                            # 4.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 4.3 touch.
                            else:
                                r = [r1[0], r1[1]]
                                r.sort()
                            #print_roots(r)
                        # 4. an endpoint of a segment intersects the other segment twice.
                        elif len(r1) == 0 and len(r2) == 2 and len(r3) == 0 and len(r4) == 0:
                            # 4.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r2[0], r2[1]):
                                I = Interval(min(r2[0], r2[1]), max(r2[0], r2[1]), True, True)
                                r = [I]
                            # 4.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 4.3 touch.
                            else:
                                r = [r2[0], r2[1]]
                                r.sort()
                        # 4. an endpoint of a segment intersects the other segment twice.
                        elif len(r1) == 0 and len(r2) == 0 and len(r3) == 2 and len(r4) == 0:
                            # 4.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r3[0], r3[1]):
                                I = Interval(min(r3[0], r3[1]), max(r3[0], r3[1]), True, True)
                                r = [I]
                            # 4.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 4.3 touch.
                            else:
                                r = [r3[0], r3[1]]
                                r.sort()
                        # 4. an endpoint of a segment intersects the other segment twice.
                        elif len(r1) == 0 and len(r2) == 0 and len(r3) == 0 and len(r4) == 2:
                            # 4.1 msegs intersect.
                            if msegs_intersect_at_midpoint(msu1, msu2, r4[0], r4[1]):
                                I = Interval(min(r4[0], r4[1]), max(r4[0], r4[1]), True, True)
                                r = [I]
                            # 4.2 collinear.
                            #elif (d1 * d2) == 0 or (d3 * d4) == 0:
							#   ...
                            # 4.3 touch.
                            else:
                                r = [r4[0], r4[1]]
                                r.sort()
                        # 5. .
                    else:
                        pass

                    # need to sort the intersections in the future, when working with 1+ units.

                    # temp
                    s += r

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

    # sort intersections.

    IT = None

    if prev_it != None and len(prev_it) > 0 and len(s) > 0:
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

                #print(x1.to_string(), x2.to_string())

                if ix1 < ix2:
                    _sorted += [x1]
                    i += 1
                elif ix3 < ix0:
                    _sorted += [x2]
                    j += 1
                # overlap
                else:
                    _sorted += [Interval(min(ix0, ix2), max(ix1, ix3), True, True)]
                    i += 1
                    j += 1
                #sys.exit()
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

                #print(x1, ix0, ix1, x2, isinstance(x2, Interval))

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

        last = _sorted[len(_sorted)-1]

        while i < n:
            #_sorted += [prev_it[i]]
            if isinstance(last, Interval) and isinstance(prev_it[i], Interval):
                if last.intersects(prev_it[i]):
                    ix0 = last.begin()
                    ix1 = last.end()
                    ix2 = prev_it[i].begin()
                    ix3 = prev_it[i].end()
                    #print(_sorted[len(_sorted)-1])
                    I = Interval(min(ix0, ix2), max(ix1, ix3), True, True)
                    _sorted[len(_sorted)-1] = I
                    #print(_sorted[len(_sorted)-1])
                else:
                    _sorted += [prev_it[i]]
            elif isinstance(last, Interval):
                if prev_it[i] > last.y:
                    _sorted += [prev_it[i]]
            else:
                _sorted += [prev_it[i]]

            last = _sorted[len(_sorted)-1]
            i += 1

        while j < m:
            if isinstance(last, Interval) and isinstance(s[j], Interval):
                if last.intersects(s[j]):
                    ix0 = last.begin()
                    ix1 = last.end()
                    ix2 = s[j].begin()
                    ix3 = s[j].end()
                    #print(_sorted[len(_sorted)-1])
                    I = Interval(min(ix0, ix2), max(ix1, ix3), True, True)
                    _sorted[len(_sorted)-1] = I
                    #print(_sorted[len(_sorted)-1])
                else:
                    _sorted += [s[j]]
            elif isinstance(last, Interval):
                if s[j] > last.y:
                    _sorted += [s[j]]
            else:
                _sorted += [s[j]]

            last = _sorted[len(_sorted)-1]
            j += 1

        IT = _sorted
    elif prev_it != None and len(prev_it) > 0 and len(s) == 0:
        IT = prev_it
    elif prev_it == None:
        IT = s

    """
    print('')
    for I in s:
        if isinstance(I, Interval):
            print(I.to_string())
        else:
            print(I)
    """

    e_exec_time = time.time()
    solver_exec_time += e_exec_time - s_exec_time

    return IT, s

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

def mseg_mseg_it_test():
    #s1 = '1,2,7,5.5,12,8#7,5,16.5,6.9,25,7#1000,2000:1000,2000'
    #s2 = '1,2,7,5.5,12,8#9,1,11.5,2.5,13,4#1000,2000:1000,2000'
    #s3 = '7,5,16.5,6.9,25,7#9,1,11.5,2.5,13,4#1000,2000:1000,2000'

    #s1 = '1,1,3,3,5,5#1,1,3,3,5,5#1000,2000:1000,2000'
    #s2 = '5,1,3,3,1,5#5,1,3,3,1,5#1000,2000:1000,2000'

    # Tests with Intersection

    # 1. (touch, intersect, touch, disjoint)
    # intersection (both points of a segment intersect the other segment. <no intersection, intersection, no intersection>
    #s1 = '1,1,10,-1,20,2#4,7,11,11,18,9#1000,2000:1000,2000'
    #s2 = '22,1,15,0,12,-1#19,8,16,9,11,5#1000,2000:1000,2000'

    #s1 = '1,1,7,0,14,1#7,7,9.5,6,12,7#1000,2000:1000,2000'

    # 2. (touch, intersect, disjoint)
    #s1 = '1,1,7,0,14,1#7,7,9,6,10,7#1000,2000:1000,2000'
    #s2 = '10,6,6,5,2,7#8,10,7,9,6,8#1000,2000:1000,2000'

    # 3. (disjoint)
    #s1 = '1,1,7,0,14,1#7,7,9,6,10,7#1000,2000:1000,2000'
    #s2 = '8,8,12,3,16,2#15,7,16,6,17,5#1000,2000:1000,2000'

    # 4. (touch, intersect, touch, disjoint) the same endpoint toches twice
    #s1 = '1,1,3,0,5,1#5,7,6,5,7,7#1000,2000:1000,2000'
    #s2 = '6.4,6.4,3,3,8,2#10,6.5,11,6,12,5.5#1000,2000:1000,2000'

    # 5. (touch, intersect)
    s1 = '1,1,4,0,7,1#7,7,9,6,10,7#1000,2000:1000,2000'
    s2 = '10,2,9,1,8,2#8,10,7,9,6,8#1000,2000:1000,2000'

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

    MS = [ms1, ms2]
    intersections = []

    intersections = get_msegs_intersections(ms1, ms2, interval)

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
        print("Exec. Time: "+ format(solver_exec_time, precision) + "sec, NE: " + str(solver_exec_times))

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

    if point.within(region):
        inicial_state = State.Inside

    region = loads(fregion_wkt)

    x0 = float(component1[0])
    y0 = float(component1[1])

    point = shapely.geometry.Point(x0, y0)

    if point.within(region):
        final_state = State.Inside

    return inicial_state, final_state

def get_mr_states(p0_wkt, q0_wkt, p1_wkt, q1_wkt):
    inicial_state = None
    final_state = None

    r0 = loads(p0_wkt)
    r1 = loads(p1_wkt)

    """
    print(len(r0.exterior.coords))
    print(len(r1.exterior.coords))
    sys.exit()
    """

    if r1.touches(r0):
        inicial_state = State.Touch
    elif r1.within(r0):
        inicial_state = State.Inside
    elif r1.equals(r0):
        inicial_state = State.Equals
    elif r1.intersects(r0):
        inicial_state = State.Intersect

    r0 = loads(q0_wkt)
    r1 = loads(q1_wkt)

    if r1.touches(r0):
        final_state = State.Touch
    elif r1.within(r0):
        final_state = State.Inside
    elif r1.equals(r0):
        final_state = State.Equals
    elif r1.intersects(r0):
        final_state = State.Intersect

    return inicial_state, final_state

def get_ms_states(ms1, ms2, ms3, ms4):
    inicial_state = None
    final_state = None

    if ms1.touches(ms2):
        inicial_state = State.Touch
    elif ms1.equals(ms2):
        inicial_state = State.Equals
    elif ms1.intersects(ms2):
        inicial_state = State.Intersect

    if ms3.touches(ms4):
        inicial_state = State.Touch
    elif ms3.equals(ms4):
        inicial_state = State.Equals
    elif ms3.intersects(ms4):
        inicial_state = State.Intersect

    return inicial_state, final_state

def get_msegs_intersections_up(ms1, ms2, i, prev_it = None):
    global solver_exec_time
    global solver_exec_times
    global epsilon

    s = []

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

        # found an intersection

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

                        #f = (((Bx - Ax) * (Cy - Ay)) - ((By - Ay) * (Cx - Ax)))
                        exec_time, r1 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Bx - Ax) * (Dy - Ay)) - ((By - Ay) * (Dx - Ax)))
                        exec_time, r2 = get_solutions_quartic_dir(c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Dx - Cx) * (Ay - Cy)) - ((Dy - Cy) * (Ax - Cx)))
                        exec_time, r3 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        exec_time, r4 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #print(r1, r2, r3, r4)

                        r1 = get_valid_roots(msu1, msu2, r1, 1)
                        r2 = get_valid_roots(msu1, msu2, r2, 2)
                        r3 = get_valid_roots(msu1, msu2, r3, 3)
                        r4 = get_valid_roots(msu1, msu2, r4, 4)

                        #print(r1, r2, r3, r4)
                        #sys.exit()

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
                        #exec_time, r1 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c0_cp0_x, c0_cp1_x, c0_cp2_x, c0_cp0_y, c0_cp1_y, c0_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

                        #f = (((Dx - Cx) * (By - Cy)) - ((Dy - Cy) * (Bx - Cx)))
                        #exec_time, r2 = get_solutions(f, t, it)
                        #exec_time, r2 = get_solutions_quartic_dir(c2_cp0_x, c2_cp1_x, c2_cp2_x, c2_cp0_y, c2_cp1_y, c2_cp2_y, c3_cp0_x, c3_cp1_x, c3_cp2_x, c3_cp0_y, c3_cp1_y, c3_cp2_y, c1_cp0_x, c1_cp1_x, c1_cp2_x, c1_cp0_y, c1_cp1_y, c1_cp2_y, msu1_t0, msu1_dt, msu2_t0, msu2_dt, it)

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
                                r = [_it]
                        else:
                            r = r + r0
                            r.sort()
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

        # Next unit(s)

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

def left_index(coords):
    
    minn = 0
    
    for i in range(1, len(coords)): 
        if coords[i][0] < coords[minn][0]: 
            minn = i 
        elif coords[i][0] == coords[minn][0]: 
            if coords[i][1] > coords[minn][1]: 
                minn = i
    
    return minn 

def mr_mr_equals(MS0, MS1, initial_state, final_state, op = 1):
    global epsilon
    msegs0 = []
    msegs1 = []

    for ms in MS0:
        msegs0 += [create_moving_segment([ms], pass_through_control_points)]

    for ms in MS1:
        msegs1 += [create_moving_segment([ms], pass_through_control_points)]

    intersections = None

    ms = msegs0[0]
    for ms1 in msegs1:
        intersections = get_msegs_equals(ms, ms1, interval, intersections)
        #roots = get_msegs_intersections(ms, ms1, interval, roots)

    #if initial_state == State.Equald:

    #intersections = None

    #N = len(roots)

    #print(intersections)
    #sys.exit()
    #intersections = [1500]

    _intersections = []

    for intersection in intersections:
        reg1 = get_region_at(msegs0, intersection)
        reg2 = get_region_at(msegs1, intersection)

        N = len(reg1.exterior.coords)
        M = len(reg2.exterior.coords)

        if N != M:
            continue

        reg1 = shapely.geometry.polygon.orient(reg1)
        reg2 = shapely.geometry.polygon.orient(reg2)

        i1 = left_index(reg1.exterior.coords)
        i2 = left_index(reg2.exterior.coords)

        idx1 = i1
        idx2 = i2

        coords1 = reg1.exterior.coords
        coords2 = reg2.exterior.coords

        dist = distance(coords1[idx1][0], coords1[idx1][1], coords2[idx2][0], coords2[idx2][1])
        if dist > epsilon:
            continue

        idx1 += 1
        idx2 += 1

        if idx1 > N - 1:
            idx1 = 0

        if idx2 > M - 1:
            idx2 = 0

        eq = True

        while idx1 != i1:
            #print(N, M, idx1, idx2)
            dist = distance(coords1[idx1][0], coords1[idx1][1], coords2[idx2][0], coords2[idx2][1])

            if dist > epsilon:
                eq = False
                break

            idx1 += 1
            idx2 += 1

            if idx1 > N - 1:
                idx1 = 0

            if idx2 > M - 1:
                idx2 = 0

        #print(i1, i2)

        #if reg1.equals(reg2):
        #    print('equal')
        #    _intersections += [intersection]

        if eq:
            _intersections += [intersection]

        #diff = reg1.difference(reg2)

        #print(diff.wkt + ';', diff.area)
        #print(reg2.wkt + ';')

    intersections = _intersections

    if intersections == None:
        intersections = []

    #print(intersections)
    #sys.exit()

    #initial_state == State.Touch

    get_samples_for_out(msegs0, msegs1, interval, n_samples, intersections)
    #get_samples_for_viz_2(msegs, mp, interval, n_samples, intersections)

    if print_intersection_information:
        print(get_intersection_information(intersections, msegs0, msegs1, op))

    if print_solver_execution_time:
        print("Exec. Time: "+ format(solver_exec_time, precision) + "sec, NE: " + str(solver_exec_times))

    sys.exit()

def get_mr_mr_intersections(MS0, MS1, initial_state, final_state, op = 1):

    msegs0 = []
    msegs1 = []

    for ms in MS0:
        msegs0 += [create_moving_segment([ms], pass_through_control_points)]

    for ms in MS1:
        msegs1 += [create_moving_segment([ms], pass_through_control_points)]

    intersections = None

    within = []

    for ms0 in msegs0:
        for ms1 in msegs1:
            intersections = get_msegs_intersections(ms0, ms1, interval, intersections)
            #intersections = get_msegs_intersections_up(ms1, ms2, interval, intersections)
            #intersections = get_intersections_3(ms0, ms1, interval, intersections)

    #print(initial_state, final_state, len(intersections), intersections[0].to_string())
    #sys.exit()

    # touch once at the beginning
    if initial_state == State.Touch and len(intersections) == 1:
        pass
    elif initial_state == State.Intersect and len(intersections) == 1:
        t = intersections[0]
        if isinstance(t, Interval):
            intersections = [Interval(interval.begin(), t.y, True, True)]
        else:
            intersections = [Interval(interval.begin(), t, True, True)]
    elif initial_state == State.Touch and final_state == State.Inside and len(intersections) == 1:
        intersections = [Interval(interval.begin(), interval.end(), True, True)]
        #within = [Interval(interval.begin(), interval.end(), True, True)]
        within = intersections
        #intersections = [interval.begin()]
    #elif (initial_state == State.Inside or initial_state == State.Intersect) and len(intersections) == 0:
    #    intersections = [Interval(interval.begin(), interval.end(), True, True)]
    # always inside.
    elif initial_state == State.Inside and len(intersections) == 0:
        intersections = [Interval(interval.begin(), interval.end(), True, True)]
        within = intersections
    elif initial_state == State.Inside and len(intersections) == 1:
        t = intersections[0]

        if isinstance(t, Interval):
            intersections = [Interval(interval.begin(), t.y, True, True)]
            within = [Interval(interval.begin(), t.x, True, True)]
        else:
            intersections = [Interval(interval.begin(), t, True, True)]
            within = [Interval(interval.begin(), t, True, True)]
    elif initial_state == State.Inside and len(intersections) > 1:
        # Process first intersection
        t = intersections[0]

        if isinstance(t, Interval):
            if t.x > interval.begin():
                I = Interval(interval.begin(), t.x, True, True)
                within = [I] + within
                intersections[0] = Interval(interval.begin(), t.y, True, True)
        else:
            print_error(-1, 'initial_state = Inside, but first intersection is not an Interval.')

        # Process the other intersections

        N = len(intersections)
        K = 0

        _intersections = []

        while K < N - 1:
            I0 = intersections[K]
            I1 = intersections[K+1]

            if isinstance(I0, Interval) and isinstance(I1, Interval):
                t = (I0.y + I1.x) / 2

                reg = get_region_at(msegs0, t)
                vertex = get_vertex_at(msegs1, t)

                if vertex.within(reg):
                    I = Interval(I0.y, I1.x, True, True)
                    within += [I]

                    I = Interval(I0.x, I1.y, True, True)
                    _intersections += [I]
                    K += 1
                else:
                    _intersections += [I0]
                    
            #elif isinstance(I0, Interval):
            #    _intersections += [I0]
            #elif isinstance(I1, Interval):
            #    _intersections += [I1]
            else:
                _intersections += [I0]

            K += 1

        intersections = _intersections

        """
        first = intersections[0]

        if isinstance(first, Interval):
            if first.x > interval.begin():
                #I = Interval(interval.begin(), first.x, True, False)
                I = Interval(interval.begin(), first.x, True, True)
                within = [I] + within
                intersections[0] = Interval(interval.begin(), first.y, True, True)
        else:
            print_error(-1, 'initial_state == State.Inside, but first intersection is not an Interval. TODO!')
        """
    elif final_state == State.Inside and len(intersections) == 0:
        print_error(-1, 'final_state = Inside, but no intersections where found.')
    elif final_state == State.Inside and len(intersections) == 1:
        t = intersections[0]

        if isinstance(t, Interval):
            I = Interval(t.y, interval.end(), True, True)
            within += [I]
            intersections[0] = Interval(t.x, interval.end(), True, True)
        else:
            # check this condition. if it has only one intersection it must touch inside?
            """
            I = Interval(t, interval.end(), True, True)
            within += [I]
            intersections[0] = Interval(t.x, interval.end(), True, True)
            """
            print_error(-1, 'TODO!')
    elif final_state == State.Inside and len(intersections) > 1:
        last = intersections[len(intersections)-1]

        if isinstance(last, Interval):
            if last.y < interval.end():
                I = Interval(last.y, interval.end(), True, True)
                within += [I]
                intersections[len(intersections)-1] = Interval(last.x, interval.end(), True, True)
        else:
            print_error(-1, 'final_state = Inside, but last intersection is not an Interval. TODO!')

        #

        N = len(intersections)
        K = 0

        _intersections = []

        while K < N - 1:
            I0 = intersections[K]
            I1 = intersections[K+1]

            if isinstance(I0, Interval) and isinstance(I1, Interval):
                t = (I0.y + I1.x) / 2

                reg = get_region_at(msegs0, t)
                vertex = get_vertex_at(msegs1, t)

                if vertex.within(reg):
                    I = Interval(I0.y, I1.x, True, True)
                    within += [I]

                    I = Interval(I0.x, I1.y, True, True)
                    _intersections += [I]
                    K += 1
                else:
                    _intersections += [I0]
            else:
                _intersections += [I0]

            K += 1

        intersections = _intersections

    # within when not inside in the begin and end.
    elif initial_state == None and len(intersections) > 1:
        N = len(intersections)
        K = 0

        _intersections = []

        while K < N - 1:
            I0 = intersections[K]
            I1 = intersections[K+1]

            if isinstance(I0, Interval) and isinstance(I1, Interval):
                t = (I0.y + I1.x) / 2

                reg = get_region_at(msegs0, t)
                vertex = get_vertex_at(msegs1, t)

                if vertex.within(reg):
                    I = Interval(I0.y, I1.x, True, True)
                    within += [I]

                    I = Interval(I0.x, I1.y, True, True)
                    _intersections += [I]
                    K += 1
                else:
                    # need to check if the other mr is inside as well.
                    reg = get_region_at(msegs1, t)
                    vertex = get_vertex_at(msegs0, t)

                    if vertex.within(reg):
                        I = Interval(I0.y, I1.x, True, True)
                        within += [I]

                        I = Interval(I0.x, I1.y, True, True)
                        _intersections += [I]
                        K += 1
                    else:
                        _intersections += [I0]
            #elif isinstance(I0, Interval):
            #    _intersections += [I0]
            #elif isinstance(I1, Interval):
            #    _intersections += [I0]
            else:
                _intersections += [I0]

            K += 1

        intersections = _intersections

    #intersections = [interval.begin()] + intersections

    #if initial_state == State.Inside:
    #    intersections = [interval.begin()] + intersections

    """
    for I in intersections:
        if isinstance(I, Interval):
            print(I.to_string())
        else:
            print(I)
    """

    #sys.exit()

    n = len(intersections)

    """
    if final_state == State.Inside:
        if n == 0:
            print_error(-1, 'final_state is Inside but no intersections were found!')
        else:
           I = intersections[n-1]

           if isinstance(I, Interval):

           else:
               if I < interval.end():
                   intersections += [interval.end()]
    """

    # find intervals of intersection

    # touched or entered the region

    # add final state to intersections if applicable.
    """
    if n == 1 and intersections[0] != interval.y:
        if final_state == State.Inside:
            I = Interval(intersections[0], interval.y, True, True)
            intersections = [I]
    """
    # this condition is in the ifs before!
    if n == 1 and final_state == State.Inside:
        t = intersections[0]

        if isinstance(t, Interval):
            if t.y != interval.y:
                I = Interval(t.x, interval.y, True, True)
                intersections = [I]

                # need to check this condition. the object may be already inside
                # in t
                I = Interval(t.y, interval.y, True, True)
                within += [I]
        elif t != interval.y:
            # check this condition. if it has only one intersection it must touch inside?
            print_error(-1, 'TODO!')
            """
            I = Interval(t, interval.y, True, True)
            intersections = [I]

            I = Interval(t, interval.y, True, True)
            within += [I]
            """
    elif n > 1:
        """
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
        """

        t = intersections[n - 1]

        if isinstance(t, Interval):
            if t.y != interval.y and final_state == State.Inside:
                I = Interval(t.x, interval.y, True, True)
                intersections[n - 1] = [I]

                # need to check this condition. the object may be already inside
                # in t
                I = Interval(t.y, interval.y, True, True)
                within += [I]
        # intersect at a time instant
        elif t != interval.y and final_state == State.Inside:
            I = Interval(t, interval.y, True, True)
            intersections[n - 1] = [I]

            I = Interval(t, interval.y, True, True)
            within += [I]

    #intersection_geom = None

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
    elif op == Operation.Within.value or \
		 op == Operation.Contains.value or \
		 op == Operation.CoveredBy.value or \
		 op == Operation.Covers.value:
        intersections = within
    elif op == Operation.Touches.value:
        touch = []
        N = len(intersections)

        if N > 0:
            for intersection in intersections:
                if isinstance(intersection, Interval):
                    # interval beginning
                    if intersection.x == interval.x:
                        if initial_state == State.Touch:
                            touch += [intersection.x]
                        # if initially inside ignore
                    else:
                        touch += [intersection.x]

                    # interval end
                    if intersection.y == interval.y:
                        if final_state == State.Touch:
                            touch += [intersection.y]
                        # if inside in the end ignore
                    else:
                        touch += [intersection.y]
                else:
                    touch += [intersection]

        intersections = touch
    elif op == Operation.Overlaps.value:
        U = len(intersections)
        V = len(within)
        a = 0
        b = 0

        overlap = []

        if U == 0:
            pass
        elif V == 0:
            if initial_state == State.Intersect:
                t = intersections[0]

                if isinstance(t, Interval):
                    overlap += [Interval(interval.begin(), t.y, True, False)]

                a = 1
                while a < U:
                    if a == U-1 and final_state == State.Intersect:
                        t = intersections[a]
                        overlap += [Interval(t.x, interval.end(), False, True)]
                    else:
                        overlap += [intersections[a]]

                    a += 1
            else:
                a = 0
                while a < U:
                    t = intersections[a]
                    if isinstance(t, Interval):
                        if a == U-1 and final_state == State.Intersect:
                            t = intersections[a]
                            overlap += [Interval(t.x, interval.end(), False, True)]
                        else:
                            overlap += [Interval(t.x, t.y, False, False)]

                    a += 1
        else:
            while a < U and b < V:
                i0 = intersections[a]
                i1 = within[b]

                if not isinstance(i0, Interval):
                    a += 1
                    continue

                if i0.equals(i1):
                    a += 1
                    b += 1
                    continue

                if i0.intersects(i1):
                    if i0.x < i1.x:
                        overlap += [Interval(i0.x, i1.x, False, False)]

                        if i0.y == i1.y:
                            a += 1
                            b += 1
                        # should not happen
                        elif i0.y < i1.y:
                            print_error(-1, "Within end is bigger than Intersections end.")
                            #a += 1
                        else:
                            intersections[a] = Interval(i1.y, i0.y, False, False)
                            b += 1
                    elif i0.x == i1.x:
                        if i0.y < i1.y:
                            print_error(-1, "Within end is bigger than Intersections end.")
                        else:
                            intersections[a] = Interval(i1.y, i0.y, False, False)
                            b += 1
                    elif i1.x > i0.x:
                        print_error(-1, "Within begin is bigger than Intersections begin.")
                else:
                    if i0.y < i1.y:
                        overlap += [i0]
                        a += 1
                    else:
                        b += 1

            while a < U:
                i0 = intersections[a]
                overlap += [i0]
                a += 1

        intersections = overlap

        """
        N = len(intersections)

        if N > 0:
            comp = []
            K = 0

            for intersection in intersections:
                if not isinstance(intersection, Interval):
                    K += 1
                    continue

                if K == 0:
                    if initial_state == State.Touch and N > 1:
                        I = Interval(intersection.x, intersection.y, False, False)
                        comp += [I]
                    elif initial_state == State.Touch and N == 1:
                        if final_state == State.Touch or final_state == None:
                            I = Interval(intersection.x, intersection.y, False, False)
                            comp += [I]
                        else:
                            I = Interval(intersection.x, intersection.y, False, True)
                            comp += [I]
                    elif initial_state == State.Inside or initial_state == State.Intersect:
                        if N > 1:
                            I = Interval(intersection.x, intersection.y, True, False)
                            comp += [I]
                        else:
                            if final_state == State.Touch or final_state == None:
                                I = Interval(intersection.x, intersection.y, True, False)
                                comp += [I]
                            else:
                                I = Interval(intersection.x, intersection.y, True, True)
                                comp += [I]
                    else:
                        if N > 1:
                            I = Interval(intersection.x, intersection.y, False, False)
                            comp += [I]
                        else:
                            if final_state == State.Touch or final_state == None:
                                I = Interval(intersection.x, intersection.y, False, False)
                                comp += [I]
                            else:
                                I = Interval(intersection.x, intersection.y, False, True)
                                comp += [I]
                elif K == N - 1:
                    if final_state == State.Touch or final_state == None:
                        I = Interval(intersection.x, intersection.y, False, False)
                        comp += [I]
                    else:
                        I = Interval(intersection.x, intersection.y, False, True)
                        comp += [I]
                else:
                    I = Interval(intersection.x, intersection.y, False, False)
                    comp += [I]

                K += 1

            intersections = comp
        """

    """
    elif op == STOperation.Intersection.value:
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
    #sys.exit()
    #get_msegs_samples_for_viz(MS, interval, n_samples, intersections)

    #if print_intersection_information:
    #    print(get_msegs_intersection_information(MS, intersections))

    get_samples_for_out(msegs0, msegs1, interval, n_samples, intersections)
    #get_samples_for_viz_2(msegs, mp, interval, n_samples, intersections)

    if print_intersection_information:
        print(get_intersection_information(intersections, msegs0, msegs1, op))

    if print_solver_execution_time:
        print("Exec. Time: "+ format(solver_exec_time, precision) + "sec, NE: " + str(solver_exec_times))

    """
    if op == STOperation.Intersection.value:
        print(intersection_geom.wkt)
    """

    sys.exit()

def get_ms_ms_intersections(msegs0, msegs1, initial_state, final_state, op = 1):
    """
    msegs0 = []
    msegs1 = []

    for ms in MS0:
        msegs0 += [create_moving_segment([ms], pass_through_control_points)]

    for ms in MS1:
        msegs1 += [create_moving_segment([ms], pass_through_control_points)]
    """

    intersections = None

    within = []

    for ms0 in msegs0:
        for ms1 in msegs1:
            intersections = get_msegs_intersections(ms0, ms1, interval, intersections)
            #intersections = get_msegs_intersections_up(ms1, ms2, interval, intersections)
            #intersections = get_intersections_3(ms0, ms1, interval, intersections)

    #print(initial_state, final_state, len(intersections), intersections[0].to_string())
    #sys.exit()

    # touch once at the beginning
    if initial_state == State.Touch and len(intersections) == 1:
        pass
    elif initial_state == State.Intersect and len(intersections) == 1:
        t = intersections[0]
        if isinstance(t, Interval):
            intersections = [Interval(interval.begin(), t.y, True, True)]
        else:
            intersections = [Interval(interval.begin(), t, True, True)]
    elif initial_state == State.Touch and final_state == State.Inside and len(intersections) == 1:
        intersections = [Interval(interval.begin(), interval.end(), True, True)]
        #within = [Interval(interval.begin(), interval.end(), True, True)]
        within = intersections
        #intersections = [interval.begin()]
    #elif (initial_state == State.Inside or initial_state == State.Intersect) and len(intersections) == 0:
    #    intersections = [Interval(interval.begin(), interval.end(), True, True)]
    # always inside.
    elif initial_state == State.Inside and len(intersections) == 0:
        intersections = [Interval(interval.begin(), interval.end(), True, True)]
        within = intersections
    elif initial_state == State.Inside and len(intersections) == 1:
        t = intersections[0]

        if isinstance(t, Interval):
            intersections = [Interval(interval.begin(), t.y, True, True)]
            within = [Interval(interval.begin(), t.x, True, True)]
        else:
            intersections = [Interval(interval.begin(), t, True, True)]
            within = [Interval(interval.begin(), t, True, True)]
    elif initial_state == State.Inside and len(intersections) > 1:
        # Process first intersection
        t = intersections[0]

        if isinstance(t, Interval):
            if t.x > interval.begin():
                I = Interval(interval.begin(), t.x, True, True)
                within = [I] + within
                intersections[0] = Interval(interval.begin(), t.y, True, True)
        else:
            print_error(-1, 'initial_state = Inside, but first intersection is not an Interval.')

        # Process the other intersections

        N = len(intersections)
        K = 0

        _intersections = []

        while K < N - 1:
            I0 = intersections[K]
            I1 = intersections[K+1]

            if isinstance(I0, Interval) and isinstance(I1, Interval):
                t = (I0.y + I1.x) / 2

                reg = get_region_at(msegs0, t)
                vertex = get_vertex_at(msegs1, t)

                if vertex.within(reg):
                    I = Interval(I0.y, I1.x, True, True)
                    within += [I]

                    I = Interval(I0.x, I1.y, True, True)
                    _intersections += [I]
                    K += 1
                else:
                    _intersections += [I0]
                    
            #elif isinstance(I0, Interval):
            #    _intersections += [I0]
            #elif isinstance(I1, Interval):
            #    _intersections += [I1]
            else:
                _intersections += [I0]

            K += 1

        intersections = _intersections

        """
        first = intersections[0]

        if isinstance(first, Interval):
            if first.x > interval.begin():
                #I = Interval(interval.begin(), first.x, True, False)
                I = Interval(interval.begin(), first.x, True, True)
                within = [I] + within
                intersections[0] = Interval(interval.begin(), first.y, True, True)
        else:
            print_error(-1, 'initial_state == State.Inside, but first intersection is not an Interval. TODO!')
        """
    elif final_state == State.Inside and len(intersections) == 0:
        print_error(-1, 'final_state = Inside, but no intersections where found.')
    elif final_state == State.Inside and len(intersections) == 1:
        t = intersections[0]

        if isinstance(t, Interval):
            I = Interval(t.y, interval.end(), True, True)
            within += [I]
            intersections[0] = Interval(t.x, interval.end(), True, True)
        else:
            # check this condition. if it has only one intersection it must touch inside?
            """
            I = Interval(t, interval.end(), True, True)
            within += [I]
            intersections[0] = Interval(t.x, interval.end(), True, True)
            """
            print_error(-1, 'TODO!')
    elif final_state == State.Inside and len(intersections) > 1:
        last = intersections[len(intersections)-1]

        if isinstance(last, Interval):
            if last.y < interval.end():
                I = Interval(last.y, interval.end(), True, True)
                within += [I]
                intersections[len(intersections)-1] = Interval(last.x, interval.end(), True, True)
        else:
            print_error(-1, 'final_state = Inside, but last intersection is not an Interval. TODO!')

        #

        N = len(intersections)
        K = 0

        _intersections = []

        while K < N - 1:
            I0 = intersections[K]
            I1 = intersections[K+1]

            if isinstance(I0, Interval) and isinstance(I1, Interval):
                t = (I0.y + I1.x) / 2

                reg = get_region_at(msegs0, t)
                vertex = get_vertex_at(msegs1, t)

                if vertex.within(reg):
                    I = Interval(I0.y, I1.x, True, True)
                    within += [I]

                    I = Interval(I0.x, I1.y, True, True)
                    _intersections += [I]
                    K += 1
                else:
                    _intersections += [I0]
            else:
                _intersections += [I0]

            K += 1

        intersections = _intersections

    # within when not inside in the begin and end.
    elif initial_state == None and len(intersections) > 1:
        N = len(intersections)
        K = 0

        _intersections = []

        while K < N - 1:
            I0 = intersections[K]
            I1 = intersections[K+1]

            if isinstance(I0, Interval) and isinstance(I1, Interval):
                t = (I0.y + I1.x) / 2

                reg = get_region_at(msegs0, t)
                vertex = get_vertex_at(msegs1, t)

                if vertex.within(reg):
                    I = Interval(I0.y, I1.x, True, True)
                    within += [I]

                    I = Interval(I0.x, I1.y, True, True)
                    _intersections += [I]
                    K += 1
                else:
                    # need to check if the other mr is inside as well.
                    reg = get_region_at(msegs1, t)
                    vertex = get_vertex_at(msegs0, t)

                    if vertex.within(reg):
                        I = Interval(I0.y, I1.x, True, True)
                        within += [I]

                        I = Interval(I0.x, I1.y, True, True)
                        _intersections += [I]
                        K += 1
                    else:
                        _intersections += [I0]
            #elif isinstance(I0, Interval):
            #    _intersections += [I0]
            #elif isinstance(I1, Interval):
            #    _intersections += [I0]
            else:
                _intersections += [I0]

            K += 1

        intersections = _intersections

    #intersections = [interval.begin()] + intersections

    #if initial_state == State.Inside:
    #    intersections = [interval.begin()] + intersections

    """
    for I in intersections:
        if isinstance(I, Interval):
            print(I.to_string())
        else:
            print(I)
    """

    #sys.exit()

    n = len(intersections)

    """
    if final_state == State.Inside:
        if n == 0:
            print_error(-1, 'final_state is Inside but no intersections were found!')
        else:
           I = intersections[n-1]

           if isinstance(I, Interval):

           else:
               if I < interval.end():
                   intersections += [interval.end()]
    """

    # find intervals of intersection

    # touched or entered the region

    # add final state to intersections if applicable.
    """
    if n == 1 and intersections[0] != interval.y:
        if final_state == State.Inside:
            I = Interval(intersections[0], interval.y, True, True)
            intersections = [I]
    """
    # this condition is in the ifs before!
    if n == 1 and final_state == State.Inside:
        t = intersections[0]

        if isinstance(t, Interval):
            if t.y != interval.y:
                I = Interval(t.x, interval.y, True, True)
                intersections = [I]

                # need to check this condition. the object may be already inside
                # in t
                I = Interval(t.y, interval.y, True, True)
                within += [I]
        elif t != interval.y:
            # check this condition. if it has only one intersection it must touch inside?
            print_error(-1, 'TODO!')
            """
            I = Interval(t, interval.y, True, True)
            intersections = [I]

            I = Interval(t, interval.y, True, True)
            within += [I]
            """
    elif n > 1:
        """
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
        """

        t = intersections[n - 1]

        if isinstance(t, Interval):
            if t.y != interval.y and final_state == State.Inside:
                I = Interval(t.x, interval.y, True, True)
                intersections[n - 1] = [I]

                # need to check this condition. the object may be already inside
                # in t
                I = Interval(t.y, interval.y, True, True)
                within += [I]
        # intersect at a time instant
        elif t != interval.y and final_state == State.Inside:
            I = Interval(t, interval.y, True, True)
            intersections[n - 1] = [I]

            I = Interval(t, interval.y, True, True)
            within += [I]

    #intersection_geom = None

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
    elif op == Operation.Within.value or \
		 op == Operation.Contains.value or \
		 op == Operation.CoveredBy.value or \
		 op == Operation.Covers.value:
        intersections = within
    elif op == Operation.Touches.value:
        touch = []
        N = len(intersections)

        if N > 0:
            for intersection in intersections:
                if isinstance(intersection, Interval):
                    # interval beginning
                    if intersection.x == interval.x:
                        if initial_state == State.Touch:
                            touch += [intersection.x]
                        # if initially inside ignore
                    else:
                        touch += [intersection.x]

                    # interval end
                    if intersection.y == interval.y:
                        if final_state == State.Touch:
                            touch += [intersection.y]
                        # if inside in the end ignore
                    else:
                        touch += [intersection.y]
                else:
                    touch += [intersection]

        intersections = touch
    elif op == Operation.Overlaps.value:
        U = len(intersections)
        V = len(within)
        a = 0
        b = 0

        overlap = []

        if U == 0:
            pass
        elif V == 0:
            if initial_state == State.Intersect:
                t = intersections[0]

                if isinstance(t, Interval):
                    overlap += [Interval(interval.begin(), t.y, True, False)]

                a = 1
                while a < U:
                    if a == U-1 and final_state == State.Intersect:
                        t = intersections[a]
                        overlap += [Interval(t.x, interval.end(), False, True)]
                    else:
                        overlap += [intersections[a]]

                    a += 1
            else:
                a = 0
                while a < U:
                    t = intersections[a]
                    if isinstance(t, Interval):
                        if a == U-1 and final_state == State.Intersect:
                            t = intersections[a]
                            overlap += [Interval(t.x, interval.end(), False, True)]
                        else:
                            overlap += [Interval(t.x, t.y, False, False)]

                    a += 1
        else:
            while a < U and b < V:
                i0 = intersections[a]
                i1 = within[b]

                if not isinstance(i0, Interval):
                    a += 1
                    continue

                if i0.equals(i1):
                    a += 1
                    b += 1
                    continue

                if i0.intersects(i1):
                    if i0.x < i1.x:
                        overlap += [Interval(i0.x, i1.x, False, False)]

                        if i0.y == i1.y:
                            a += 1
                            b += 1
                        # should not happen
                        elif i0.y < i1.y:
                            print_error(-1, "Within end is bigger than Intersections end.")
                            #a += 1
                        else:
                            intersections[a] = Interval(i1.y, i0.y, False, False)
                            b += 1
                    elif i0.x == i1.x:
                        if i0.y < i1.y:
                            print_error(-1, "Within end is bigger than Intersections end.")
                        else:
                            intersections[a] = Interval(i1.y, i0.y, False, False)
                            b += 1
                    elif i1.x > i0.x:
                        print_error(-1, "Within begin is bigger than Intersections begin.")
                else:
                    if i0.y < i1.y:
                        overlap += [i0]
                        a += 1
                    else:
                        b += 1

            while a < U:
                i0 = intersections[a]
                overlap += [i0]
                a += 1

        intersections = overlap

        """
        N = len(intersections)

        if N > 0:
            comp = []
            K = 0

            for intersection in intersections:
                if not isinstance(intersection, Interval):
                    K += 1
                    continue

                if K == 0:
                    if initial_state == State.Touch and N > 1:
                        I = Interval(intersection.x, intersection.y, False, False)
                        comp += [I]
                    elif initial_state == State.Touch and N == 1:
                        if final_state == State.Touch or final_state == None:
                            I = Interval(intersection.x, intersection.y, False, False)
                            comp += [I]
                        else:
                            I = Interval(intersection.x, intersection.y, False, True)
                            comp += [I]
                    elif initial_state == State.Inside or initial_state == State.Intersect:
                        if N > 1:
                            I = Interval(intersection.x, intersection.y, True, False)
                            comp += [I]
                        else:
                            if final_state == State.Touch or final_state == None:
                                I = Interval(intersection.x, intersection.y, True, False)
                                comp += [I]
                            else:
                                I = Interval(intersection.x, intersection.y, True, True)
                                comp += [I]
                    else:
                        if N > 1:
                            I = Interval(intersection.x, intersection.y, False, False)
                            comp += [I]
                        else:
                            if final_state == State.Touch or final_state == None:
                                I = Interval(intersection.x, intersection.y, False, False)
                                comp += [I]
                            else:
                                I = Interval(intersection.x, intersection.y, False, True)
                                comp += [I]
                elif K == N - 1:
                    if final_state == State.Touch or final_state == None:
                        I = Interval(intersection.x, intersection.y, False, False)
                        comp += [I]
                    else:
                        I = Interval(intersection.x, intersection.y, False, True)
                        comp += [I]
                else:
                    I = Interval(intersection.x, intersection.y, False, False)
                    comp += [I]

                K += 1

            intersections = comp
        """

    """
    elif op == STOperation.Intersection.value:
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
    #sys.exit()
    #get_msegs_samples_for_viz(MS, interval, n_samples, intersections)

    #if print_intersection_information:
    #    print(get_msegs_intersection_information(MS, intersections))

    return intersections

    get_samples_for_out(msegs0, msegs1, interval, n_samples, intersections)
    #get_samples_for_viz_2(msegs, mp, interval, n_samples, intersections)

    if print_intersection_information:
        print(get_intersection_information(intersections, msegs0, msegs1, op))

    if print_solver_execution_time:
        print("Exec. Time: "+ format(solver_exec_time, precision) + "sec, NE: " + str(solver_exec_times))

    """
    if op == STOperation.Intersection.value:
        print(intersection_geom.wkt)
    """

    sys.exit()

def get_ms_ms_intersections2(msegs0, msegs1, initial_state, final_state, op = 1, idx = 0, reg_dict = None):
    intersections = None

    within = []
    MSEG = []
    II = []
    D = 0

    IDICT = {}

    for ms0 in msegs0:
        for ms1 in msegs1:
            intersections, intersection = get_msegs_intersections2(ms0, ms1, interval, intersections)

            #mms1 = LineString([(x1, y1), (x4, y4)])
            mms1 = ms1.obj_at(interval.begin())
            mms2 = ms0.obj_at(interval.begin())
            #mms3 = LineString([(x3, y3), (x6, y6)])
            mms3 = ms1.obj_at(interval.end())
            mms4 = ms0.obj_at(interval.end())

            initial_state, final_state = get_ms_states(mms1, mms2, mms3, mms4)

            #intersections = get_ms_ms_intersections([ms], [ms1], initial_state, final_state, 1)

            if intersection != None and len(intersection) > 0:
                """
                t = Symbol('t')
                x = Symbol('x')

                msu1 = ms.units[0]
                msu2 = ms1.units[0]

                T = (t - msu1.i.x) / (msu1.i.y - msu1.i.x)

                Ax, Ay = msu1.c0.curves[0].at(T)
                Bx, By = msu1.c1.curves[0].at(T)

                Cx, Cy = msu2.c0.curves[0].at(T)
                Dx, Dy = msu2.c1.curves[0].at(T)

                m1 = (By - Ay) / (Bx - Ax)
                m2 = (Dy - Cy) / (Dx - Cx)

                b1 = Ay - m1 * Ax
                b2 = Cy - m2 * Cx

                g = (m1 * x + (Ay - m1 * Ax)) - (m2 * x + (Cy - m2 * Cx))

                r = solve(g, x, t, dict=True)
                #exec 'def get_xx(t): return ' + str(r[0].get(x))

                F += [str(r[0].get(x))]
                """
                #print(D)
                MSEG += [(ms0, ms1, D, idx)]
                II += [intersection]

                if D in IDICT:
                    e = IDICT[D]
                    #e = IDICT[idx]
                    #e += [ms0, D, len(II) - 1]
                    #e += [[D, len(II) - 1]]
                    e += [[len(II) - 1]]
                else:
                    #IDICT[idx] = [ms0, D, len(II) - 1]
                    #IDICT[idx] = [[D, len(II) - 1]]
                    IDICT[D] = [[len(II) - 1]]

                if reg_dict != None:
                    if D in reg_dict:
                        e = reg_dict[D]
                        #e += [ms1, D, len(II) - 1]
                        e += [[idx, len(II) - 1]]
                    else:
                        #reg_dict[D] = [ms1, idx, len(II) - 1]
                        reg_dict[D] = [[idx, len(II) - 1]]

        D += 1

    # touch once at the beginning
    if initial_state == State.Touch and len(intersections) == 1:
        pass
    elif initial_state == State.Intersect and len(intersections) == 1:
        t = intersections[0]
        if isinstance(t, Interval):
            intersections = [Interval(interval.begin(), t.y, True, True)]
        else:
            intersections = [Interval(interval.begin(), t, True, True)]
    elif initial_state == State.Touch and final_state == State.Inside and len(intersections) == 1:
        intersections = [Interval(interval.begin(), interval.end(), True, True)]
        #within = [Interval(interval.begin(), interval.end(), True, True)]
        within = intersections
        #intersections = [interval.begin()]
    #elif (initial_state == State.Inside or initial_state == State.Intersect) and len(intersections) == 0:
    #    intersections = [Interval(interval.begin(), interval.end(), True, True)]
    # always inside.
    elif initial_state == State.Inside and len(intersections) == 0:
        intersections = [Interval(interval.begin(), interval.end(), True, True)]
        within = intersections
    elif initial_state == State.Inside and len(intersections) == 1:
        t = intersections[0]

        if isinstance(t, Interval):
            intersections = [Interval(interval.begin(), t.y, True, True)]
            within = [Interval(interval.begin(), t.x, True, True)]
        else:
            intersections = [Interval(interval.begin(), t, True, True)]
            within = [Interval(interval.begin(), t, True, True)]
    elif initial_state == State.Inside and len(intersections) > 1:
        # Process first intersection
        t = intersections[0]

        if isinstance(t, Interval):
            if t.x > interval.begin():
                I = Interval(interval.begin(), t.x, True, True)
                within = [I] + within
                intersections[0] = Interval(interval.begin(), t.y, True, True)
        else:
            print_error(-1, 'initial_state = Inside, but first intersection is not an Interval.')

        # Process the other intersections

        N = len(intersections)
        K = 0

        _intersections = []

        while K < N - 1:
            I0 = intersections[K]
            I1 = intersections[K+1]

            if isinstance(I0, Interval) and isinstance(I1, Interval):
                t = (I0.y + I1.x) / 2

                reg = get_region_at(msegs0, t)
                vertex = get_vertex_at(msegs1, t)

                if vertex.within(reg):
                    I = Interval(I0.y, I1.x, True, True)
                    within += [I]

                    I = Interval(I0.x, I1.y, True, True)
                    _intersections += [I]
                    K += 1
                else:
                    _intersections += [I0]
                    
            #elif isinstance(I0, Interval):
            #    _intersections += [I0]
            #elif isinstance(I1, Interval):
            #    _intersections += [I1]
            else:
                _intersections += [I0]

            K += 1

        intersections = _intersections
    elif final_state == State.Inside and len(intersections) == 0:
        print_error(-1, 'final_state = Inside, but no intersections where found.')
    elif final_state == State.Inside and len(intersections) == 1:
        t = intersections[0]

        if isinstance(t, Interval):
            I = Interval(t.y, interval.end(), True, True)
            within += [I]
            intersections[0] = Interval(t.x, interval.end(), True, True)
        else:
            # check this condition. if it has only one intersection it must touch inside?
            """
            I = Interval(t, interval.end(), True, True)
            within += [I]
            intersections[0] = Interval(t.x, interval.end(), True, True)
            """
            print_error(-1, 'TODO!')
    elif final_state == State.Inside and len(intersections) > 1:
        last = intersections[len(intersections)-1]

        if isinstance(last, Interval):
            if last.y < interval.end():
                I = Interval(last.y, interval.end(), True, True)
                within += [I]
                intersections[len(intersections)-1] = Interval(last.x, interval.end(), True, True)
        else:
            print_error(-1, 'final_state = Inside, but last intersection is not an Interval. TODO!')

        #

        N = len(intersections)
        K = 0

        _intersections = []

        while K < N - 1:
            I0 = intersections[K]
            I1 = intersections[K+1]

            if isinstance(I0, Interval) and isinstance(I1, Interval):
                t = (I0.y + I1.x) / 2

                reg = get_region_at(msegs0, t)
                vertex = get_vertex_at(msegs1, t)

                if vertex.within(reg):
                    I = Interval(I0.y, I1.x, True, True)
                    within += [I]

                    I = Interval(I0.x, I1.y, True, True)
                    _intersections += [I]
                    K += 1
                else:
                    _intersections += [I0]
            else:
                _intersections += [I0]

            K += 1

        intersections = _intersections

    # within when not inside in the begin and end.
    elif initial_state == None and len(intersections) > 1:
        N = len(intersections)
        K = 0

        _intersections = []

        while K < N - 1:
            I0 = intersections[K]
            I1 = intersections[K+1]

            if isinstance(I0, Interval) and isinstance(I1, Interval):
                t = (I0.y + I1.x) / 2

                reg = get_region_at(msegs0, t)
                vertex = get_vertex_at(msegs1, t)

                if vertex.within(reg):
                    I = Interval(I0.y, I1.x, True, True)
                    within += [I]

                    I = Interval(I0.x, I1.y, True, True)
                    _intersections += [I]
                    K += 1
                else:
                    # need to check if the other mr is inside as well.
                    reg = get_region_at(msegs1, t)
                    vertex = get_vertex_at(msegs0, t)

                    if vertex.within(reg):
                        I = Interval(I0.y, I1.x, True, True)
                        within += [I]

                        I = Interval(I0.x, I1.y, True, True)
                        _intersections += [I]
                        K += 1
                    else:
                        _intersections += [I0]
            #elif isinstance(I0, Interval):
            #    _intersections += [I0]
            #elif isinstance(I1, Interval):
            #    _intersections += [I0]
            else:
                _intersections += [I0]

            K += 1

        intersections = _intersections

    n = len(intersections)

    # find intervals of intersection

    # this condition is in the ifs before!
    if n == 1 and final_state == State.Inside:
        t = intersections[0]

        if isinstance(t, Interval):
            if t.y != interval.y:
                I = Interval(t.x, interval.y, True, True)
                intersections = [I]

                # need to check this condition. the object may be already inside
                # in t
                I = Interval(t.y, interval.y, True, True)
                within += [I]
        elif t != interval.y:
            # check this condition. if it has only one intersection it must touch inside?
            print_error(-1, 'TODO!')
    elif n > 1:
        t = intersections[n - 1]

        if isinstance(t, Interval):
            if t.y != interval.y and final_state == State.Inside:
                I = Interval(t.x, interval.y, True, True)
                intersections[n - 1] = [I]

                # need to check this condition. the object may be already inside
                # in t
                I = Interval(t.y, interval.y, True, True)
                within += [I]
        # intersect at a time instant
        elif t != interval.y and final_state == State.Inside:
            I = Interval(t, interval.y, True, True)
            intersections[n - 1] = [I]

            I = Interval(t, interval.y, True, True)
            within += [I]

    return intersections, MSEG, II, IDICT

def get_x(t):
    #return (6*t**2 + 13*t + 8) / (5*t + 4)
    return t / 2 + 2

def get_y(x1, y1, x2, y2, dx1, dx2, dy1, dy2, t, x):
    m = (y2 - y1 + t *(dy2 - dy1)) / (x2 - x1 + t *(dx2 - dx1))
    b = y1 + dy1 * t - m * (x1 + dx1 * t)

    return m * x + b

def get_xxx(t):
    #t = 1000
    #print(t, -(t**6 + 2250.0*t**5 - 56375000.0*t**4 + 208000000000.0*t**3 - 311000000000000.0*t**2 + 1.88625e+17*t - 3.75e+19)/(3375000.0*t**4 - 20250000000.0*t**3 + 36250000000000.0*t**2 - 1.7625e+16*t + 7.5e+17))
    #sys.exit()
    return -(t**6 + 2250.0*t**5 - 56375000.0*t**4 + 208000000000.0*t**3 - 311000000000000.0*t**2 + 1.88625e+17*t - 3.75e+19)/(3375000.0*t**4 - 20250000000.0*t**3 + 36250000000000.0*t**2 - 1.7625e+16*t + 7.5e+17)
    #([t, x], set([(t, (-8.0*t**6 - 66.0*t**5 + 241.0*t**4 - 200.0*t**3 - 98.0*t**2 + 141.0*t + 40.0)/(27.0*t**4 - 54.0*t**3 - 34.0*t**2 + 61.0*t + 20.0))]))

def get_yy(ms, t, x):
    Ax, Ay, Bx, By = ms.at(t)
    m = (By - Ay) / (Bx - Ax)
    b = Ay - m * Ax

    #print(x, t, m, b, m * x + b)
    #sys.exit()
    return m * x + b

def get_states_mp_mr(iregion, fregion, ipoint, fpoint):
    inicial_state = None
    final_state = None

    if ipoint.touches(iregion):
        inicial_state = State.Touch
    elif ipoint.within(iregion):
        inicial_state = State.Inside

    if fpoint.touches(fregion):
        final_state = State.Touch
    elif fpoint.within(fregion):
        final_state = State.Inside

    return inicial_state, final_state

"""

	"POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))"
	"POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))"
	"POLYGON((879.41392092742944442 729.71448703117766854, 889.59586843560805391 719.23611292160808262, 905.30234479740443021 716.51898401674543493, 915.69536819172503783 720.30301183894971473, 919.65333894372611212 729.96845561698000893, 914.43391940942797191 734.93882689411861975, 913.08115780326852473 743.50976093106328335, 907.10894991356440187 745.86812153907453649, 903.46665239345543341 752.06605014146452959, 894.28654149784210858 754.96664410872506323, 886.51609268522088314 753.56158382969033482, 874.69227938276412715 747.81969845663002161, 865.6532279740820286 749.37989383540730159, 862.54327071581406017 752.79927334168314701, 858.65736615717491986 753.99565981920409286, 855.74808947198516762 752.74425405949409651, 855.01914955103779903 748.80008871936524883, 855.73428406011316838 742.3498703605157516, 863.61937324107020686 733.62936271821831724, 879.41392092742944442 729.71448703117766854))"
	"POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))"

    python mr_mr3.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "Polygon ((748.80098648344142021 733.46200304065894215, 760.84418475839777329 725.18977514549726493, 776.77832191718437116 725.61340492996339435, 786.22463162522683433 731.36675480059125221, 788.20523617735966582 741.62168247015733868, 782.11054426960947694 745.46897521405162479, 779.09922089530255107 753.60671481200563449, 772.77992586063794533 754.74497756731545905, 767.99025418557687317 760.10591922251308006, 758.41905820139072603 761.1451924546150849, 751.07646438292408675 758.23995835831522072, 740.61218070717939099 750.28567801360395606, 731.44280049178235004 750.03844036630630399, 727.72131581929954791 752.77970689633741586, 723.67604402899030447 753.1888168876311056, 721.06955344101311312 751.38989665004146445, 721.13022164038488881 747.3793963061679051, 723.09944923275418205 741.19563717984669893, 732.54503161323282256 734.1954330096382364, 748.80098648344142021 733.46200304065894215))" "Polygon ((958.96950724370094576 591.32745931417821339, 973.11009655979603394 570.4387693834488573, 985.778314790770537 560.01697802276305538, 996.86654358164435052 559.38213668256196343, 1003.35323895748501855 565.86883205840263145, 1001.44538737635537018 574.0725938572600171, 1005.8686271803173895 581.96778186931248911, 1007.27439169793888141 588.05942811233887824, 1006.45900714589788549 592.44823461685598431, 1000.49146158579060284 597.72995346326729305, 996.60099443451656498 608.88556911413843409, 986.7549302016573165 615.09140285154671801, 977.97881292846113865 615.66375832588562389, 971.11054723639449549 618.33475053946710887, 968.63034018092594124 623.4859498085170344, 965.5777776511185948 625.39380138964668276, 962.14364480508527322 624.05830528285594028, 961.38050417263343661 619.86103180437078208, 958.36668505313252808 615.7586434986490076, 958.96950724370094576 591.32745931417821339))" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"

	Equals = Within and Contains

	Usage examples:

	0. DIID
	python mr_mr_pred.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "Polygon ((748.80098648344142021 733.46200304065894215, 760.84418475839777329 725.18977514549726493, 776.77832191718437116 725.61340492996339435, 786.22463162522683433 731.36675480059125221, 788.20523617735966582 741.62168247015733868, 782.11054426960947694 745.46897521405162479, 779.09922089530255107 753.60671481200563449, 772.77992586063794533 754.74497756731545905, 767.99025418557687317 760.10591922251308006, 758.41905820139072603 761.1451924546150849, 751.07646438292408675 758.23995835831522072, 740.61218070717939099 750.28567801360395606, 731.44280049178235004 750.03844036630630399, 727.72131581929954791 752.77970689633741586, 723.67604402899030447 753.1888168876311056, 721.06955344101311312 751.38989665004146445, 721.13022164038488881 747.3793963061679051, 723.09944923275418205 741.19563717984669893, 732.54503161323282256 734.1954330096382364, 748.80098648344142021 733.46200304065894215))" "Polygon ((958.96950724370094576 591.32745931417821339, 973.11009655979603394 570.4387693834488573, 985.778314790770537 560.01697802276305538, 996.86654358164435052 559.38213668256196343, 1003.35323895748501855 565.86883205840263145, 1001.44538737635537018 574.0725938572600171, 1005.8686271803173895 581.96778186931248911, 1007.27439169793888141 588.05942811233887824, 1006.45900714589788549 592.44823461685598431, 1000.49146158579060284 597.72995346326729305, 996.60099443451656498 608.88556911413843409, 986.7549302016573165 615.09140285154671801, 977.97881292846113865 615.66375832588562389, 971.11054723639449549 618.33475053946710887, 968.63034018092594124 623.4859498085170344, 965.5777776511185948 625.39380138964668276, 962.14364480508527322 624.05830528285594028, 961.38050417263343661 619.86103180437078208, 958.36668505313252808 615.7586434986490076, 958.96950724370094576 591.32745931417821339))" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"
	
	1. 
	python mr_mr_pred.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))" "POLYGON((897.66840276579080182 723.73057602966605373, 911.37302495899132282 718.66582434957012993, 926.71624328398752368 722.98575960612254221, 934.46233408883995253 730.88081369568362788, 933.86648095000509784 741.30824362529267546, 927.01416985340483734 743.54269289592321002, 922.09838145801779774 750.69293056194078417, 915.69296021554362142 750.2460407078147, 909.73442882719564295 754.26804939494968494, 900.20077860583876372 752.92737983257131873, 893.7953573633645874 748.30951800660159279, 885.60237670438607438 738.03105136170131573, 876.77389204974110726 735.54177060384165543, 872.49360765002040807 737.28623493815780421, 868.47159896288553682 736.69038179932294952, 866.38611297696365909 734.30696924398375813, 867.42885596992459796 730.43392384155754371, 870.85501151822472821 724.92228230733564942, 881.72933130195985996 720.45338376607458031, 897.66840276579080182 723.73057602966605373))" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"

	1. 
	python mr_mr_pred.py
	"POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))"
	"POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))"
	"POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))"
	"POLYGON((897.66840276579080182 723.73057602966605373, 911.37302495899132282 718.66582434957012993, 926.71624328398752368 722.98575960612254221, 934.46233408883995253 730.88081369568362788, 933.86648095000509784 741.30824362529267546, 927.01416985340483734 743.54269289592321002, 922.09838145801779774 750.69293056194078417, 915.69296021554362142 750.2460407078147, 909.73442882719564295 754.26804939494968494, 900.20077860583876372 752.92737983257131873, 893.7953573633645874 748.30951800660159279, 885.60237670438607438 738.03105136170131573, 876.77389204974110726 735.54177060384165543, 872.49360765002040807 737.28623493815780421, 868.47159896288553682 736.69038179932294952, 866.38611297696365909 734.30696924398375813, 867.42885596992459796 730.43392384155754371, 870.85501151822472821 724.92228230733564942, 881.72933130195985996 720.45338376607458031, 897.66840276579080182 723.73057602966605373))"
	"1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"	

	2. 
	python mr_mr_pred.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))" "POLYGON((879.41392092742944442 729.71448703117766854, 889.59586843560805391 719.23611292160808262, 905.30234479740443021 716.51898401674543493, 915.69536819172503783 720.30301183894971473, 919.65333894372611212 729.96845561698000893, 914.43391940942797191 734.93882689411861975, 913.08115780326852473 743.50976093106328335, 907.10894991356440187 745.86812153907453649, 903.46665239345543341 752.06605014146452959, 894.28654149784210858 754.96664410872506323, 886.51609268522088314 753.56158382969033482, 874.69227938276412715 747.81969845663002161, 865.6532279740820286 749.37989383540730159, 862.54327071581406017 752.79927334168314701, 858.65736615717491986 753.99565981920409286, 855.74808947198516762 752.74425405949409651, 855.01914955103779903 748.80008871936524883, 855.73428406011316838 742.3498703605157516, 863.61937324107020686 733.62936271821831724, 879.41392092742944442 729.71448703117766854))" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"
	
	3. 
	python mr_mr_pred.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "POLYGON((879.41392092742944442 729.71448703117766854, 889.59586843560805391 719.23611292160808262, 905.30234479740443021 716.51898401674543493, 915.69536819172503783 720.30301183894971473, 919.65333894372611212 729.96845561698000893, 914.43391940942797191 734.93882689411861975, 913.08115780326852473 743.50976093106328335, 907.10894991356440187 745.86812153907453649, 903.46665239345543341 752.06605014146452959, 894.28654149784210858 754.96664410872506323, 886.51609268522088314 753.56158382969033482, 874.69227938276412715 747.81969845663002161, 865.6532279740820286 749.37989383540730159, 862.54327071581406017 752.79927334168314701, 858.65736615717491986 753.99565981920409286, 855.74808947198516762 752.74425405949409651, 855.01914955103779903 748.80008871936524883, 855.73428406011316838 742.3498703605157516, 863.61937324107020686 733.62936271821831724, 879.41392092742944442 729.71448703117766854))" "POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"
	
	4. (starts intersecting) > disjoint
	python mr_mr_pred.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "POLYGON((879.41392092742944442 729.71448703117766854, 889.59586843560805391 719.23611292160808262, 905.30234479740443021 716.51898401674543493, 915.69536819172503783 720.30301183894971473, 919.65333894372611212 729.96845561698000893, 914.43391940942797191 734.93882689411861975, 913.08115780326852473 743.50976093106328335, 907.10894991356440187 745.86812153907453649, 903.46665239345543341 752.06605014146452959, 894.28654149784210858 754.96664410872506323, 886.51609268522088314 753.56158382969033482, 874.69227938276412715 747.81969845663002161, 865.6532279740820286 749.37989383540730159, 862.54327071581406017 752.79927334168314701, 858.65736615717491986 753.99565981920409286, 855.74808947198516762 752.74425405949409651, 855.01914955103779903 748.80008871936524883, 855.73428406011316838 742.3498703605157516, 863.61937324107020686 733.62936271821831724, 879.41392092742944442 729.71448703117766854))" "POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"
	
	
	python mr_mr_pred.py "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))" "POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))" "Polygon ((748.80098648344142021 733.46200304065894215, 760.84418475839777329 725.18977514549726493, 776.77832191718437116 725.61340492996339435, 786.22463162522683433 731.36675480059125221, 788.20523617735966582 741.62168247015733868, 782.11054426960947694 745.46897521405162479, 779.09922089530255107 753.60671481200563449, 772.77992586063794533 754.74497756731545905, 767.99025418557687317 760.10591922251308006, 758.41905820139072603 761.1451924546150849, 751.07646438292408675 758.23995835831522072, 740.61218070717939099 750.28567801360395606, 731.44280049178235004 750.03844036630630399, 727.72131581929954791 752.77970689633741586, 723.67604402899030447 753.1888168876311056, 721.06955344101311312 751.38989665004146445, 721.13022164038488881 747.3793963061679051, 723.09944923275418205 741.19563717984669893, 732.54503161323282256 734.1954330096382364, 748.80098648344142021 733.46200304065894215))" "Polygon ((932.4503702659993678 710.56818313477924676, 946.0186041077555501 684.71907909311289586, 958.68682233873005316 674.29728773242709394, 972.63201132314020469 671.92190611627131602, 978.34545570971511097 679.61551318884789907, 979.61324330652439585 687.91110357542618203, 979.2118478789150231 695.70014508377175844, 978.44122091149188236 702.41211204753801667, 979.36751469385740165 706.72854432652002288, 976.54506807043003391 714.22144767861823311, 967.57241462362674156 721.17246096067196959, 953.55784171455206888 726.71113613842362611, 946.71206106563249705 731.82014465729207586, 943.59623950511331714 738.04523826288630062, 941.25498631411483075 740.59626443417869268, 938.684763640097799 742.28562162740399799, 935.52075032066886706 742.37160522305021004, 933.06284195302146145 741.01198536867400435, 931.84754807543095012 734.99936731925004096, 932.4503702659993678 710.56818313477924676))" "1" "1" "1" "100" "1000,2000" "0.0000001" "2" "1"		
	
"""

def solve_nl():
    x1 = 1
    y1 = 1

    x2 = 0.2
    y2 = 0.75

    x3 = -1
    y3 = 3

    x4 = 3
    y4 = 3

    x5 = 2
    y5 = 4.5

    x6 = 1
    y6 = 5

    """
    uinterval = Interval(i.begin(), i.end(), True, False)

    unit = str(x1) + ',' + str(y1) + ',' + str(x3) + ',' + str(y3) + ',' + str(x5) + ',' + str(y5) + '#'
    unit += str(x2) + ',' + str(y2) + ',' + str(x4) + ',' + str(y4) + ',' + str(x6) + ',' + str(y6) + '#'
    unit += str(uinterval.begin()) + ',' + str(uinterval.end()) + ':' + str(uinterval.begin()) + ',' + str(uinterval.end())
    """

    unit = [[[x1, y1, x2, y2, x3, y3], [x4, y4, x5, y5, x6, y6], interval.begin(), interval.end()], [interval.begin(), interval.end()]]

    """
    u = str(x1) + ',' + str(y1) + ',' + str(x2) + ',' + str(y2) + ',' + str(x3) + ',' + str(y3) + '#'
    u += str(x4) + ',' + str(y4) + ',' + str(x5) + ',' + str(y5) + ',' + str(x6) + ',' + str(y6) + '#'
    u += str(interval.x) + ',' + str(interval.y) + ':' + str(interval.x) + ',' + str(interval.y)

    unit1 = [u]
    """

    units = [unit]

    #ms1 = create_moving_segment(unit1, pass_through_control_points)
    ms1 = create_moving_segment2([], pass_through_control_points, units)

    #unit2 = ['3,1,4,2.5,5,4#1,3,2,4.5,3,6#1000,2000:1000,2000']

    x7 = 3
    y7 = 1

    x8 = 4.5
    y8 = 1.5

    x9 = 5
    y9 = 4

    x10 = 1
    y10 = 3

    x11 = 2
    y11 = 4.5

    x12 = 3
    y12 = 6

    """
    u = str(x7) + ',' + str(y7) + ',' + str(x8) + ',' + str(y8) + ',' + str(x9) + ',' + str(y9) + '#'
    u += str(x10) + ',' + str(y10) + ',' + str(x11) + ',' + str(y11) + ',' + str(x12) + ',' + str(y12) + '#'
    u += str(interval.x) + ',' + str(interval.y) + ':' + str(interval.x) + ',' + str(interval.y)

    unit2 = [u]
    """

    unit = [[[x7, y7, x8, y8, x9, y9], [x10, y10, x11, y11, x12, y12], interval.begin(), interval.end()], [interval.begin(), interval.end()]]
    units = [unit]

    ms2 = create_moving_segment2([], pass_through_control_points, units)
    #ms2 = create_moving_segment(unit2, pass_through_control_points)

    mms1 = LineString([(x1, y1), (x4, y4)])
    mms2 = LineString([(x7, y7), (x10, y10)])
    mms3 = LineString([(x3, y3), (x6, y6)])
    mms4 = LineString([(x9, y9), (x12, y12)])

    initial_state, final_state = get_ms_states(mms1, mms2, mms3, mms4)

    t = Symbol('t')
    x = Symbol('x')

    msu1 = ms1.units[0]
    msu2 = ms2.units[0]

    T = (t - msu1.i.x) / (msu1.i.y - msu1.i.x)

    Ax, Ay = msu1.c0.curves[0].at(T)
    Bx, By = msu1.c1.curves[0].at(T)

    Cx, Cy = msu2.c0.curves[0].at(T)
    Dx, Dy = msu2.c1.curves[0].at(T)

    m1 = (By - Ay) / (Bx - Ax)
    m2 = (Dy - Cy) / (Dx - Cx)

    b1 = Ay - m1 * Ax
    b2 = Cy - m2 * Cx

    g = (m1 * x + (Ay - m1 * Ax)) - (m2 * x + (Cy - m2 * Cx))

    #g = x * (m1 - m2) + b1 - b2
    r = solve(g, x, t, dict=True)
    #print(r, m1, m2, b1, b2, g)
    #print(r, g)
    #print(r)
    #[{x: (-8.0*t**6 - 66.0*t**5 + 241.0*t**4 - 200.0*t**3 - 98.0*t**2 + 141.0*t + 40.0)/(27.0*t**4 - 54.0*t**3 - 34.0*t**2 + 61.0*t + 20.0)}]
    #([t, x], set([(t, (6*t**2 + 13*t + 8)/(5*t + 4))]))
    #t = 1
    #h = x*(-(t + 2)/(-t - 2) + (t + 2)/(2 - t)) - (1 - 2*t)*(t + 2)/(2 - t) + (t + 2)*(2*t + 3)/(-t - 2)
    #print(h)

    #print(r[0])
    #print(r[0].get(x))

    #for x in r[0]:
    #  print(x)

    #for x, y in r[0].items():
    #  print(x, y)
  
    #sys.exit()
    #-(t**6 + 2250.0*t**5 - 56375000.0*t**4 + 208000000000.0*t**3 - 311000000000000.0*t**2 + 1.88625e+17*t - 3.75e+19)/(3375000.0*t**4 - 20250000000.0*t**3 + 36250000000000.0*t**2 - 1.7625e+16*t + 7.5e+17)
    # linear

    #d = {}

    #exec 'def get_xx(t): return -(t**6 + 2250.0*t**5 - 56375000.0*t**4 + 208000000000.0*t**3 - 311000000000000.0*t**2 + 1.88625e+17*t - 3.75e+19)/(3375000.0*t**4 - 20250000000.0*t**3 + 36250000000000.0*t**2 - 1.7625e+16*t + 7.5e+17)' #in d
    #exec 'def get_xx(t): return ' + str(r[0].get(x))

    #print('def get_xx(t): return ' + str(r[0].get(x)))
    #print(r[0].get(x), str(r[0].get(x)))

    #(-8.0*t**6 - 66.0*t**5 + 241.0*t**4 - 200.0*t**3 - 98.0*t**2 + 141.0*t + 40.0)/(27.0*t**4 - 54.0*t**3 - 34.0*t**2 + 61.0*t + 20.0)

    #(-8.0*t**6 - 66.0*t**5 + 241.0*t**4 - 200.0*t**3 - 98.0*t**2 + 141.0*t + 40.0)/(27.0*t**4 - 54.0*t**3 - 34.0*t**2 + 61.0*t + 20.0), 
    #(-8.0*t**6 - 66.0*t**5 + 241.0*t**4 - 200.0*t**3 - 98.0*t**2 + 141.0*t + 40.0)/(27.0*t**4 - 54.0*t**3 - 34.0*t**2 + 61.0*t + 20.0)

    #d = {'x':1000}
    #print(d['f'])
    #print(get_xx(1000))
    #sys.exit()

    return ms1, ms2, initial_state, final_state, str(r[0].get(x))

def test_nl(ms1, ms2, initial_state, final_state, interval, n_samples):
    operation = 1
    intersections = get_ms_ms_intersections([ms1], [ms2], initial_state, final_state, operation)

    get_samples_for_out3([ms1], [ms2], interval, n_samples, intersections, ms1)

    if print_intersection_information:
        print(get_intersection_information(intersections, [ms1], [ms2], operation))

    if print_solver_execution_time:
        print("Exec. Time: "+ format(solver_exec_time, precision) + "sec, NE: " + str(solver_exec_times))

    sys.exit()

def create_moving_point10(units):
    global p_linear_traj
    global pass_through_control_points

    mp = MovingPoint()

    for u in units:
        N = len(u)
        i = Interval(u[N - 1][0], u[N - 1][1], True, False)

        k = 0
        while k < N - 1:
            _u = u[k]

            position = _u[0]
            ui_t0 = _u[1]
            ui_t1 = _u[2]

            ci = Interval(ui_t0, ui_t1, True, False)

            if len(position) == 4:
                x0 = position[0]
                y0 = position[1]

                x1 = position[2]
                y1 = position[3]

                p0 = Point(x0, y0)
                p1 = Point(x1, y1)

                msu = MPU([p0, p1], i)
                mp.add_unit(msu)
            elif len(position) == 6:
                x0 = position[0]
                y0 = position[1]

                x1 = position[2]
                y1 = position[3]

                x2 = position[4]
                y2 = position[5]

                cc = CCurve()

                p0 = Point(x0, y0)
                p1 = Point(x1, y1)
                p2 = Point(x2, y2)

                t = 0.5

                if pass_through_control_points:
                    x = 2 * p1.x - t * p0.x - t * p2.x
                    y = 2 * p1.y - t * p0.y - t * p2.y
                    c = QuadBezierCurve(p0, Point(x, y), p2)
                else:
                    c = QuadBezierCurve(p0, p1, p2)

                #print(ci.to_string(), i.to_string())

                cc.add_curve(c, ci)
                msu = MPU2(cc, i)
                mp.add_unit(msu)
            else:
                print(u)
                print("ERR: Invalid unit data.")
                sys.exit()

            k += 1

    """
    N = len(units)
    i = Interval(units[N - 1][0], units[N - 1][1], True, False)

    mp = MovingPoint()

    k = 0
    while k < N - 1:
        u = units[k]

        position = u[0]
        ui_t0 = u[1]
        ui_t1 = u[2]

        ci = Interval(ui_t0, ui_t1, True, False)

        if len(position) == 4:
            x0 = position[0]
            y0 = position[1]

            x1 = position[2]
            y1 = position[3]

            p0 = Point(x0, y0)
            p1 = Point(x1, y1)

            msu = MPU([p0, p1], i)
            mp.add_unit(msu)
        elif len(position) == 6:
            x0 = position[0]
            y0 = position[1]

            x1 = position[2]
            y1 = position[3]

            x2 = position[4]
            y2 = position[5]

            cc = CCurve()

            p0 = Point(x0, y0)
            p1 = Point(x1, y1)
            p2 = Point(x2, y2)

            t = 0.5

            if pass_through_control_points:
                x = 2 * p1.x - t * p0.x - t * p2.x
                y = 2 * p1.y - t * p0.y - t * p2.y
                c = QuadBezierCurve(p0, Point(x, y), p2)
            else:
                c = QuadBezierCurve(p0, p1, p2)

            cc.add_curve(c, ci)
            msu = MPU2(cc, i)
            mp.add_unit(msu)
        else:
            print(u)
            print("ERR: Invalid unit data.")
            sys.exit()

        k += 1
    """

    return mp

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

    return intersections

def get_mr_mp_intersections2(msegs, mp, initial_state, final_state, op = 1, p_linear_traj = False):
    #msegs = []

    #for ms in MS:
    #    msegs += [create_moving_segment([ms], pass_through_control_points)]

    intersections = None

    #print('20')

    if p_linear_traj:
        #print('30')
        for ms in msegs:
            intersections = get_intersections_4(ms, mp, interval, intersections)
    else:
        for ms in msegs:    
            intersections = get_intersections_3(ms, mp, interval, intersections)

    #print('10')

    if initial_state == State.Inside or initial_state == State.Touch:# or initial_state == State.Intersect:
        intersections = [interval.begin()] + intersections

    if final_state == State.Inside or final_state == State.Touch:# or final_state == State.Intersect:
        intersections += [interval.end()]

    intersections = process_intersections(intersections, mp, msegs, initial_state, final_state)

    return intersections

def get_F(MS, ms1, interval):
    F = []
    intersections = None

    for ms0 in MS:
        intersections, intersection = get_msegs_intersections2(ms0, ms1, interval, intersections)

        mms1 = ms1.obj_at(interval.begin())
        mms2 = ms0.obj_at(interval.begin())
        mms3 = ms1.obj_at(interval.end())
        mms4 = ms0.obj_at(interval.end())

        initial_state, final_state = get_ms_states(mms1, mms2, mms3, mms4)

        if intersection != None and len(intersection) > 0:
            t = Symbol('t')
            x = Symbol('x')

            msu1 = ms0.units[0]
            msu2 = ms1.units[0]

            T = (t - msu1.i.x) / (msu1.i.y - msu1.i.x)

            Ax, Ay = msu1.c0.curves[0].at(T)
            Bx, By = msu1.c1.curves[0].at(T)

            Cx, Cy = msu2.c0.curves[0].at(T)
            Dx, Dy = msu2.c1.curves[0].at(T)

            m1 = (By - Ay) / (Bx - Ax)
            m2 = (Dy - Cy) / (Dx - Cx)

            b1 = Ay - m1 * Ax
            b2 = Cy - m2 * Cx

            g = (m1 * x + (Ay - m1 * Ax)) - (m2 * x + (Cy - m2 * Cx))
            """
            print('')
            print(m1)
            print(b1)
            print((m1 * x + (Ay - m1 * Ax)))
            print(g)
            print('')
            """
            r = solve(g, x, t, dict=True)

            F += [str(r[0].get(x))]

    return F

def union_periods(pa, pb):

    if pa == None or len(pa) == 0:
        return pb

    if pb == None or len(pb) == 0:
        return pa

    i = 0
    j = 0

    _sorted = []

    n = len(pa)
    m = len(pb)

    while i < n and j < m:
        x1 = pa[i]
        x2 = pb[j]

        if isinstance(x1, Interval) and isinstance(x2, Interval):
            # disjoint
            if x1.end() < x2.begin():
                _sorted += [x1]
                i += 1
            # disjoint
            elif x2.end() < x1.begin():
                _sorted += [x2]
                j += 1
            # overlap
            else:
                _sorted += [Interval(min(x1.begin(), x2.begin()), max(x1.end(), x2.end()), True, True)]
                i += 1
                j += 1
        elif isinstance(x1, Interval):
            if x2 < x1.begin():
                _sorted += [x2]
                j += 1
            elif x2 > x1.end():
                _sorted += [x1]
                i += 1
            else:
                #_sorted += [x1]
                #i += 1
                j += 1
        elif isinstance(x2, Interval):
            if x1 < x2.begin():
                _sorted += [x1]
                i += 1
            elif x1 > x2.end():
                _sorted += [x2]
                j += 1
            else:
                #_sorted += [x2]
                i += 1
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
        _sorted += [pa[i]]
        i += 1

    while j < m:
        _sorted += [pb[j]]
        j += 1

    return _sorted

def complement_period(p, it):
    R = []
    i = 0
    n = len(p)

    while i < n:
        x1 = p[i]

        if isinstance(x1, Interval):
            # first
            if i == 0:
                if x1.begin() > it.begin():
                    R += [Interval(it.begin(), x1.begin(), True, False)]
            # last
            elif i == n - 1:
                prev = p[i - 1]

                if isinstance(prev, Interval):
                    if prev.end() != x1.begin():
                        R += [Interval(prev.end(), x1.begin(), False, False)]
                else:
                    if prev != x1.begin():
                        R += [Interval(prev, x1.begin(), False, False)]

                if x1.end() < it.end():
                    R += [Interval(x1.end(), it.end(), False, True)]
            # other
            else:
                prev = p[i - 1]

                if isinstance(prev, Interval):
                    if prev.end() != x1.begin():
                        R += [Interval(prev.end(), x1.begin(), False, False)]
                else:
                    if prev != x1.begin():
                        R += [Interval(prev, x1.begin(), False, False)]
        else:
            # first
            if i == 0:
                if x1 > it.begin():
                    R += [Interval(it.begin(), x1, True, False)]
            # last
            elif i == n - 1:
                prev = p[i - 1]

                if isinstance(prev, Interval):
                    if prev.end() != x1:
                        R += [Interval(prev.end(), x1, False, False)]
                else:
                    if prev != x1:
                        R += [Interval(prev, x1, False, False)]

                if x1 < it.end():
                    R += [Interval(x1, it.end(), False, True)]
            # other
            else:
                prev = p[i - 1]

                if isinstance(prev, Interval):
                    if prev.end() != x1:
                        R += [Interval(prev.end(), x1, False, False)]
                else:
                    if prev != x1:
                        R += [Interval(prev, x1, False, False)]

        i += 1

    return R

def intersect_periods(pa, pb):

    if pa == None or len(pa) == 0:
        return pb

    if pb == None or len(pb) == 0:
        return pa

    i = 0
    j = 0

    _sorted = []

    n = len(pa)
    m = len(pb)

    while i < n and j < m:
        x1 = pa[i]
        x2 = pb[j]

        if isinstance(x1, Interval) and isinstance(x2, Interval):
            ix0 = x1.begin()
            ix1 = x1.end()
            ix2 = x2.begin()
            ix3 = x2.end()

            if ix1 < ix2:
                _sorted += [x1]
                i += 1
            elif ix3 < ix0:
                _sorted += [x2]
                j += 1
            # overlap
            else:
                _sorted += [Interval(min(ix0, ix2), max(ix1, ix3), True, True)]
                i += 1
                j += 1
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

    last = _sorted[len(_sorted)-1]

    while i < n:
        if isinstance(last, Interval) and isinstance(pa[i], Interval):
            if last.intersects(pa[i]):
                ix0 = last.begin()
                ix1 = last.end()
                ix2 = pa[i].begin()
                ix3 = pa[i].end()
    
                I = Interval(min(ix0, ix2), max(ix1, ix3), True, True)
                _sorted[len(_sorted)-1] = I
            else:
                _sorted += [pa[i]]
        elif isinstance(last, Interval):
            if pa[i] > last.y:
                _sorted += [pa[i]]
        else:
            _sorted += [pa[i]]

        last = _sorted[len(_sorted)-1]
        i += 1

    while j < m:
        if isinstance(last, Interval) and isinstance(pb[j], Interval):
            if last.intersects(pb[j]):
                ix0 = last.begin()
                ix1 = last.end()
                ix2 = pb[j].begin()
                ix3 = pb[j].end()
    
                I = Interval(min(ix0, ix2), max(ix1, ix3), True, True)
                _sorted[len(_sorted)-1] = I
            else:
                _sorted += [pb[j]]
        elif isinstance(last, Interval):
            if pb[j] > last.y:
                _sorted += [pb[j]]
        else:
            _sorted += [pb[j]]

        last = _sorted[len(_sorted)-1]
        j += 1

    return _sorted

def intersection_periods(pa, pb):

    if pa == None or len(pa) == 0:
        return []

    if pb == None or len(pb) == 0:
        return []

    i = 0
    j = 0

    _sorted = []

    n = len(pa)
    m = len(pb)

    while i < n and j < m:
        x1 = pa[i]
        x2 = pb[j]

        if isinstance(x1, Interval) and isinstance(x2, Interval):
            # disjoint
            if x1.end() < x2.begin():
                i += 1
            # disjoint
            elif x2.end() < x1.begin():
                j += 1
            # overlap
            else:
                it = x1.intersection(x2)
                if it != None:
                    _sorted += [it]

                if x1.end() < x2.end():
                    i += 1
                elif x2.end() < x1.end():
                    j += 1
                else:
                    i += 1
                    j += 1
        elif isinstance(x1, Interval):
            if x2 < x1.begin():
                j += 1
            elif x2 > x1.end():
                i += 1
            else:
                _sorted += [x2]
                j += 1
        elif isinstance(x2, Interval):
            if x1 < x2.begin():
                i += 1
            elif x1 > x2.end():
                j += 1
            else:
                _sorted += [x1]
                i += 1
        else:
            if x1 < x2:
                i += 1
            elif x1 > x2:
                j += 1
            else:
                _sorted += [x1]
                i += 1
                j += 1

    return _sorted

def intersect_periods2(pa, pb):
    # no intersection.
    if pa == None or len(pa) == 0:
        return []

    # no intersection.
    if pb == None or len(pb) == 0:
        return []

    # begin.
    i = 0
    j = 0

    intersection = []

    n = len(pa)
    m = len(pb)

    while i < n and j < m:
        x1 = pa[i]
        x2 = pb[j]

        if isinstance(x1, Interval) and isinstance(x2, Interval):
            it = x1.intersection(x2)

            if it != None:
                intersection += [it]

            if x1.end() < x2.end():
                i += 1
            elif x2.end() < x1.end():
                j += 1
            else:
                i += 1
                j += 1
        elif isinstance(x1, Interval):
            if x2 < x1.begin():
                j += 1
            elif x2 > x1.end():
                i += 1
            else:
                intersection += [x2]
                j += 1
        elif isinstance(x2, Interval):
            if x1 < x2.begin():
                i += 1
            elif x1 > x2.end():
                j += 1
            else:
                intersection += [x1]
                i += 1
        else:
            if x1 < x2:
                i += 1
            elif x1 > x2:
                j += 1
            else:
                intersection += [x1]
                i += 1
                j += 1

    #last = _sorted[len(_sorted)-1]

    """
    while i < n:
        if isinstance(last, Interval) and isinstance(pa[i], Interval):
            if last.intersects(pa[i]):
                ix0 = last.begin()
                ix1 = last.end()
                ix2 = pa[i].begin()
                ix3 = pa[i].end()
    
                I = Interval(min(ix0, ix2), max(ix1, ix3), True, True)
                _sorted[len(_sorted)-1] = I
            else:
                _sorted += [pa[i]]
        elif isinstance(last, Interval):
            if pa[i] > last.y:
                _sorted += [pa[i]]
        else:
            _sorted += [pa[i]]

        last = _sorted[len(_sorted)-1]
        i += 1

    while j < m:
        if isinstance(last, Interval) and isinstance(pb[j], Interval):
            if last.intersects(pb[j]):
                ix0 = last.begin()
                ix1 = last.end()
                ix2 = pb[j].begin()
                ix3 = pb[j].end()
    
                I = Interval(min(ix0, ix2), max(ix1, ix3), True, True)
                _sorted[len(_sorted)-1] = I
            else:
                _sorted += [pb[j]]
        elif isinstance(last, Interval):
            if pb[j] > last.y:
                _sorted += [pb[j]]
        else:
            _sorted += [pb[j]]

        last = _sorted[len(_sorted)-1]
        j += 1
    """

    return intersection

def l_most_coord(coords):
    min_coord_id = 0
    
    for i in range(1, len(coords)):
        if coords[i][0] < coords[min_coord_id][0]: 
            min_coord_id = i 
        elif coords[i][0] == coords[min_coord_id][0]: 
            if coords[i][1] < coords[min_coord_id][1]: 
                min_coord_id = i
    
    return min_coord_id 

def get_msegs_simple_polygons(p, q):
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

#def get_moving_segs_from_observations2(p, q, t0, t1, p_min_vertex_id, q_min_vertex_id):
def get_moving_segs_from_observations2(p, q, t0, t1):
    global err_msg
    global err_code
	
    # get moving segments from p to q

    msegs = get_msegs_simple_polygons_with_corr(p, q)

    # get moving segments at t = 0.5
	
    coords = []
    t = 0.5

    k = 0
    for mseg in msegs:
        xi, yi, xf, yf = mseg.at(t)

        if k == 0:
            coords += [[xi, yi]]
            k = 1

        coords += [[xf, yf]]               
            
    g = Polygon(coords)

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

def get_moving_segs_from_observations3(a, b, c, t0, t1):
    global err_msg
    global err_code
	
    g1_coords = a.exterior.coords
    g2_coords = b.exterior.coords
    g3_coords = c.exterior.coords

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

def seconds_to_time(sec):
    day = sec / (24 * 3600)
    sec = sec % (24 * 3600)
    hour = sec / 3600

    sec %= 3600
    minutes = sec / 60

    sec %= 60
    seconds = sec

    return day, hour, minutes, seconds

def test(N, p1_wkt, q1_wkt, FIND_INT_FUNC = False):
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

        """
        p0_wkt = 'POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))'
        q0_wkt = 'POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))'
        p1_wkt = p1_st
        q1_wkt = q1_st

        r0_m_segs = get_moving_segs_from_observations(p0_wkt, q0_wkt, t0, t1)

        if r0_m_segs == None:
            print_error(err_code, err_msg)

        r1_m_segs = get_moving_segs_from_observations(p1_wkt, q1_wkt, t0, t1)

        if r1_m_segs == None:
            print_error(err_code, err_msg)

        initial_state, final_state = get_mr_states(p0_wkt, q0_wkt, p1_wkt, q1_wkt)

        exec_time, solver_exec_time, avg, sec, ssec = intersections_tests(r0_m_segs, r1_m_segs, initial_state, final_state, op)
        """

        p_wkt = 'POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))'
        q_wkt = 'POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))'

        p = loads(p_wkt)
        q = loads(q_wkt)

        p1 = loads(p1_wkt)
        q1 = loads(q1_wkt)

        p = shapely.geometry.polygon.orient(p)
        q = shapely.geometry.polygon.orient(q)

        p1 = shapely.geometry.polygon.orient(p1)
        q1 = shapely.geometry.polygon.orient(q1)

        reg_m_segs = get_moving_segs_from_observations2(p, q, t0, t1)

        if reg_m_segs == None:
            print_error(err_code, err_msg)

        reg1_m_segs = get_moving_segs_from_observations2(p1, q1, t0, t1)

        if reg1_m_segs == None:
            print_error(err_code, err_msg)

        MS = []
        for ms in reg_m_segs:
            MS += [create_moving_segment([ms], pass_through_control_points)]

        #FIND_INT_FUNC = False

        TRIMS = []
        MPoints = []
        IP = []
        G = []
        Gext = 0
        for ms in reg1_m_segs:
            #TRIMS += [create_moving_segment([ms], pass_through_control_points)]

            mseg, mpt, ip, g, gex = create_moving_segment_and_mp([ms], pass_through_control_points, t0, t1, p, q, MS, FIND_INT_FUNC)
            TRIMS += [mseg]
            MPoints += [mpt]
            IP += [ip]
            G += [g]
            Gext += gex

        """
        IP = []
        G = []
        for mp in MPoints:
            x, y = mp.at(t0)
            ipoint = shapely.geometry.Point(x, y)

            x, y = mp.at(t1)
            fpoint = shapely.geometry.Point(x, y)

            mp_i_state, mp_f_state = get_states_mp_mr(p, q, ipoint, fpoint)
            it = get_mr_mp_intersections2(MS, mp, mp_i_state, mp_f_state, 1, True)
            IP += [it]
        """

        """
        if_begin_exec_time = time.time()

        FIND_INT_FUNC = False
        PRINT_TEST_INFO = False

        if FIND_INT_FUNC:
            ms1 = TRIMS[0]
            ms2 = TRIMS[1]
            ms3 = TRIMS[2]

            G = get_F(MS, ms1, interval)
            G1 = get_F(MS, ms2, interval)
            G2 = get_F(MS, ms3, interval)

        if_end_exec_time = time.time()
        """

        reg_dict = {}

        intersections = []
        M = []
        I = []
        IDICT = []

        initial_state = None
        final_state = None
        num_seg_int = 0

        for ms in TRIMS:
            intersections, M, I, IDICT = get_ms_ms_intersections2(MS, [ms], initial_state, final_state, 1, 0, reg_dict)
            num_seg_int += len(I)

        ITT = None
        for it in intersections:
            if ITT == None:
                ITT = [it]
            else:
                ITT = intersect_periods(ITT, it)

        num_int_periods = len(ITT)
        intersections = ITT

        #for it in intersections:
        #    print(it.to_string())

        proc_end_exec_time, n_invalid_geoms, n_complex_geoms = samples_for_out7(MS, G, M, I, TRIMS, interval, n_samples, intersections, IP, MPoints, reg_dict, IDICT)

        #min_exec_time = min(min_exec_time, exec_time)
        #max_exec_time = max(max_exec_time, exec_time)

        #min_solver_exec_time = min(min_solver_exec_time, solver_exec_time)
        #max_solver_exec_time = max(max_solver_exec_time, solver_exec_time)

        #t_avg += avg
        k += 1

    #t_avg = t_avg / N
    #res += [(format(min_exec_time, precision3), format(max_exec_time, precision3), format(min_solver_exec_time, precision3), format(max_solver_exec_time, precision3), format(t_avg, precision))]

    return res

#test_mseg_mseg_int()
#mseg_mseg_it_test()
#get_params()

"""
if TESTING:
    p1_wkt = 'Polygon((695.86 589.19, 747.30 568.25, 745.27 511.29, 695.86 589.19))'
    q1_wkt = 'Polygon((866.77 758.36, 938.86 706.62, 919.96 761.55, 866.77 758.36))'

    #p1_wkt = 'POLYGON((879.41392092742944442 729.71448703117766854, 889.59586843560805391 719.23611292160808262, 905.30234479740443021 716.51898401674543493, 915.69536819172503783 720.30301183894971473, 919.65333894372611212 729.96845561698000893, 914.43391940942797191 734.93882689411861975, 913.08115780326852473 743.50976093106328335, 907.10894991356440187 745.86812153907453649, 903.46665239345543341 752.06605014146452959, 894.28654149784210858 754.96664410872506323, 886.51609268522088314 753.56158382969033482, 874.69227938276412715 747.81969845663002161, 865.6532279740820286 749.37989383540730159, 862.54327071581406017 752.79927334168314701, 858.65736615717491986 753.99565981920409286, 855.74808947198516762 752.74425405949409651, 855.01914955103779903 748.80008871936524883, 855.73428406011316838 742.3498703605157516, 863.61937324107020686 733.62936271821831724, 879.41392092742944442 729.71448703117766854))'
    #q1_wkt = 'POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))'

    N = NTESTS

    FIND_INT_FUNC = False
    test(N, p1_wkt, q1_wkt, FIND_INT_FUNC)

    FIND_INT_FUNC = True
    test(N, p1_wkt, q1_wkt, FIND_INT_FUNC)

sys.exit()
"""

"""
x1t = x1 + dx1 * t
y1t = y1 + dy1 * t
x2t = x2 + dx2 * t
y2t = y2 + dy2 * t

y = m * x + b

m = (((y2 + dy2 * t) - (y1 + dy1 * t)) / ((x2 + dx2 * t) - (x1 + dx1 * t)))
b = y1 + dy1 * t - m * (x1 + dx1 * t)

y = ((((y2 + dy2 * t) - (y1 + dy1 * t)) / ((x2 + dx2 * t) - (x1 + dx1 * t))) * x + y1 + dy1 * t - (((y2 + dy2 * t) - (y1 + dy1 * t)) / ((x2 + dx2 * t) - (x1 + dx1 * t))) * (x1 + dx1 * t))


((((y2 + dy2 * t) - (y1 + dy1 * t)) / ((x2 + dx2 * t) - (x1 + dx1 * t))) * x + y1 + dy1 * t - (((y2 + dy2 * t) - (y1 + dy1 * t)) / ((x2 + dx2 * t) - (x1 + dx1 * t))) * (x1 + dx1 * t)) - 
((((y4 + dy4 * t) - (y3 + dy3 * t)) / ((x4 + dx4 * t) - (x3 + dx3 * t))) * x + y3 + dy3 * t - (((y4 + dy4 * t) - (y3 + dy3 * t)) / ((x4 + dx4 * t) - (x3 + dx3 * t))) * (x3 + dx3 * t))
"""

"""
# Test seg-seg

ms1, ms2, initial_state, final_state, f = solve_nl()

exec 'def get_xx(t): return ' + f

test_nl(ms1, ms2, initial_state, final_state, interval, n_samples)
"""

"""
import os
from pathlib2 import Path

dir = 'E:\\Anime'

for entry in os.listdir(dir):
    _dir = os.path.join(dir, entry)
    if os.path.isdir(_dir):
        print('')
        print(entry)
        avg = 0
        i = 0
        for r, d, f in os.walk(_dir):
            for file in f:
                o = Path(os.path.join(_dir, file))
                avg += o.stat().st_size
                i += 1

                print('    ' + file + '    ' + str(o.stat().st_size / (1024 * 1024)) + ' MB')

        print('    Avg size: ' + str((avg / (1024 * 1024)) / i) + ' MB')
    else:
        print('')
        o = Path(os.path.join(dir, entry))
        print(entry + '    ' + str(o.stat().st_size / (1024 * 1024)) + ' MB')

# r=root, d=directories, f = files

sys.exit()
"""

#day, hour, minutes, seconds = seconds_to_time(int(422.75))
#print('Time: ' + '{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0))
#sys.exit()

"""
s_exec_time = time.time()

...

e_exec_time = time.time()

exec_time = e_exec_time - s_exec_time
"""

proc_begin_exec_time = time.time()

get_params()

# 1. M. Region Source and Target.

p_wkt = str(sys.argv[1])
q_wkt = str(sys.argv[2])

p = loads(p_wkt)
q = loads(q_wkt)

p = shapely.geometry.polygon.orient(p)
q = shapely.geometry.polygon.orient(q)

# >>>

# 2. M. Triangle Source, Middle and Target.

tri_1_wkt = 'Polygon((695.86 589.19, 747.30 568.25, 745.27 511.29, 695.86 589.19))'
tri_2_wkt = 'Polygon((806.89 654.29, 858.05 652.84, 878.40 601.39, 806.89 654.29))'
tri_3_wkt = 'Polygon((866.77 758.36, 938.86 706.62, 919.96 761.55, 866.77 758.36))'

tri_1 = loads(tri_1_wkt)
tri_2 = loads(tri_2_wkt)
tri_3 = loads(tri_3_wkt)

tri_1 = shapely.geometry.polygon.orient(tri_1)
tri_2 = shapely.geometry.polygon.orient(tri_2)
tri_3 = shapely.geometry.polygon.orient(tri_3)

# >>>

"""
print(tri_1.wkt + ';')
print(tri_2.wkt + ';')
print(tri_3.wkt + ';')
sys.exit()
"""

t0 = 1000
t1 = 2000

# 3. Create the Moving Segments.

reg_m_segs = get_moving_segs_from_observations2(p, q, t0, t1)

if reg_m_segs == None:
    print_error(err_code, err_msg)

tri_m_segs = get_moving_segs_from_observations3(tri_1, tri_2, tri_3, t0, t1)

if tri_m_segs == None:
    print_error(err_code, err_msg)

# >>>

"""
G = []

G += ['-(1.02907253515921e+23*t**6 + 5.31369836881899e+35*t**5 - 3.8999628187391e+39*t**4 + 8.96879527225381e+42*t**3 - 8.44546981788519e+45*t**2 + 1.50189434734654e+48*t + 2.94251182433602e+51)/(5.95903676000005e+26*t**4 + 2.74442402708568e+39*t**3 - 1.11791022692127e+43*t**2 + 1.75351330443477e+46*t - 1.08777492380643e+49)']
G += ['-(4.11698576167202e+22*t**6 + 1.37154982430906e+35*t**5 - 1.10702456811311e+39*t**4 + 3.5267857030672e+42*t**3 - 5.59606881698965e+45*t**2 + 2.64340570434936e+48*t + 1.17713435085807e+51)/(2.38439420000002e+26*t**4 + 8.78799171977478e+37*t**3 - 8.62151048684832e+41*t**2 + 4.26564010551861e+45*t - 4.6905653576949e+48)']
G += ['1.0e-7*(1.26873383128982e+32*t**5 - 1.01948449126411e+36*t**4 + 3.45938823962012e+39*t**3 - 6.33523521001329e+42*t**2 + 4.19346127808539e+45*t + 5.01238433769654e+47)/(2.151731e+16*t**4 + 1.6311107024557e+28*t**3 - 5.26356611151697e+31*t**2 - 1.97953566316401e+35*t + 3.66445920552749e+38)']
G += ['-(6.1741511999355e+17*t**6 - 4.53797348838513e+34*t**5 + 3.00121669834727e+38*t**4 - 5.08556403674325e+41*t**3 + 1.54631653870367e+44*t**2 + 2.14066517831606e+47*t - 6.46051722341711e+48)/(1.07596044e+26*t**4 - 2.81769632676879e+38*t**3 + 9.881528674196e+41*t**2 - 1.08666540830647e+45*t + 1.46406847530319e+47)']
G += ['-(2.05805040002153e+17*t**6 + 1.11321866702591e+33*t**5 + 2.71735216736376e+36*t**4 - 7.6680393688116e+40*t**3 + 2.57230617427243e+44*t**2 - 3.02309799016516e+47*t + 3.16242514432002e+48)/(1.07620528e+25*t**4 + 3.42116973328559e+37*t**3 - 1.39897778140361e+41*t**2 + 1.31340023492712e+44*t + 1.36249694369895e+47)']
G += ['1.0e-7*(2.05805040000001e+17*t**6 - 3.71965937485873e+31*t**5 + 2.08246873372304e+37*t**4 - 1.9104458924902e+41*t**3 + 5.85063540666231e+44*t**2 - 6.94592212812361e+47*t + 3.6085136460727e+49)/(483359999999999.0*t**4 - 6.50577529492309e+30*t**3 + 2.9322386547884e+34*t**2 - 3.11399071137193e+37*t - 2.52079585588091e+40)']
G += ['(-2.05794749748002e+22*t**6 + 5.61009627425368e+34*t**5 - 3.44452012125147e+38*t**4 + 3.67162102846136e+41*t**3 + 8.09567773705194e+44*t**2 - 1.86325493519958e+48*t + 2.92805263303124e+50)/(1.19175748000001e+26*t**4 - 4.52098491989653e+38*t**3 + 1.87069782421074e+42*t**2 - 2.48125429398216e+45*t + 7.76677123194518e+46)']
G += ['1.0e-7*(1.44063536608431e+18*t**6 + 9.87669920260596e+33*t**5 - 4.40306334870863e+37*t**4 - 7.80830412575288e+40*t**3 + 5.28159835568447e+44*t**2 - 7.06496090692947e+47*t + 1.77448927671849e+49)/(4.3033808e+18*t**4 - 1.19591264108479e+31*t**3 + 4.69432298748775e+34*t**2 - 4.86440086402978e+37*t - 2.57395848009325e+40)']
G += ['1.0e-7*(1.85224553218411e+18*t**6 + 1.97481786465759e+34*t**5 - 1.6548666348237e+38*t**4 + 5.61993734602924e+41*t**3 - 7.5623092388509e+44*t**2 - 1.81393021220785e+47*t + 4.2514908907738e+50)/(8.60716392e+18*t**4 + 8.24377549037554e+29*t**3 + 2.63993783073588e+34*t**2 - 1.33886758478488e+38*t + 1.006039255693e+41)']
G += ['1.0e-7*(2.26385630075267e+18*t**6 + 5.7476358131235e+33*t**5 + 4.29754781313501e+37*t**4 - 1.02527127673072e+42*t**3 + 2.54595173711829e+45*t**2 + 6.24366668719428e+46*t - 1.15074220989719e+51)/(4.30375052e+19*t**4 - 6.7527876067783e+31*t**3 + 1.56352571474147e+35*t**2 + 1.87391744044417e+38*t - 2.45921054272895e+41)']
G += ['-(5.14533180504002e+21*t**6 - 1.01538922900938e+34*t**5 + 9.87310321341404e+37*t**4 - 3.19097369069936e+41*t**3 + 2.47212117564761e+44*t**2 + 4.36659864516696e+47*t - 4.5129867985723e+50)/(5.67038820000002e+25*t**4 - 6.26721154358012e+37*t**3 + 5.43091626148281e+41*t**2 - 1.38671517306398e+45*t + 9.67381793631623e+47)']
G += ['(1.02904578049863e+22*t**6 + 6.62389701482971e+33*t**5 - 6.44184708284543e+37*t**4 + 2.6227131346258e+41*t**3 - 4.55369292141767e+44*t**2 + 1.55503585879834e+47*t + 1.56688128441405e+50)/(-8.65085895000005e+25*t**4 + 2.25213156185819e+37*t**3 + 1.06360891080914e+40*t**2 - 3.93961186592996e+44*t + 4.76051706676594e+47)']

G += ['-(1.02913324764601e+24*t**6 - 1.51762200786383e+35*t**5 + 2.81100093358268e+39*t**4 - 1.93264083802111e+43*t**3 + 3.10415227346458e+46*t**2 + 2.36886094436373e+49*t - 2.70165525518223e+52)/(1.13404644000001e+28*t**4 + 7.75750830338166e+39*t**3 - 3.93186026537629e+42*t**2 - 7.4518019319288e+46*t + 5.64443582491974e+49)']
G += ['(-3.18997812000002e+20*t**6 + 1.57336209314509e+37*t**5 - 1.51029091054066e+41*t**4 + 5.39604862125874e+44*t**3 - 7.89005333993513e+47*t**2 + 1.73512149852079e+50*t + 3.24512305938231e+53)/(1.30960000000002e+24*t**4 - 3.32903248850493e+40*t**3 + 3.68763933630328e+44*t**2 - 1.18612802845519e+48*t + 1.01811112048704e+51)']
G += ['-(3.08707560000002e+18*t**6 + 5.87590826854935e+34*t**5 - 1.04445553168945e+39*t**4 + 6.028031931312e+42*t**3 - 1.24762997572977e+46*t**2 + 7.04550135557613e+48*t + 3.47428550582021e+51)/(1.68040000000001e+22*t**4 - 9.64303248850506e+38*t**3 + 8.59389336303243e+41*t**2 + 8.63593221544821e+45*t - 1.29599387951297e+49)']
G += ['-(2.05794749748001e+22*t**6 + 4.37854284278221e+34*t**5 + 3.46179923095784e+37*t**4 - 2.24368464790114e+42*t**3 + 6.51618471173132e+45*t**2 - 5.06307390902657e+48*t - 1.34487965843955e+51)/(1.1608028000001e+25*t**4 + 1.07554436156225e+39*t**3 - 2.85328813765206e+42*t**2 - 1.17643399615817e+45*t + 5.87737548921887e+48)']

G1 = []

G1 += ['(2.67809328864006e+30*t**6 - 7.30065330354299e+42*t**5 + 6.49618617982432e+46*t**4 - 1.22542091757939e+50*t**3 + 2.02009477040741e+52*t**2 - 2.35336501237242e+55*t + 2.01376315262685e+59)/(-2.96993004000007e+34*t**4 + 7.54998636955557e+46*t**3 - 2.52217226682691e+50*t**2 + 7.36405970204944e+52*t + 2.96441251750812e+56)']
G1 += ['-(2.34344875379775e+22*t**6 + 1.60662030258546e+38*t**5 - 1.1593853784811e+42*t**4 + 3.95331641375431e+44*t**3 + 3.76456982757903e+48*t**2 + 2.70999516043158e+51*t - 1.25293097602871e+55)/(2.31271425e+29*t**4 + 1.44681486124225e+42*t**3 - 1.48025050292937e+45*t**2 - 1.38809272321799e+49*t + 2.35825871613591e+52)']
G1 += ['-(3.76625688448392e+22*t**6 + 4.01548939842799e+38*t**5 - 4.45639801376339e+42*t**4 + 1.39140669836403e+46*t**3 - 1.50392028589215e+49*t**2 - 7.6947114961619e+51*t + 1.0418211279736e+54)/(5.779335375e+29*t**4 + 5.27560960184084e+42*t**3 - 2.70381865724163e+46*t**2 + 5.68914236034823e+49*t - 2.31788697296422e+52)']
G1 += ['-(3.6825619380255e+22*t**6 + 9.34954907536972e+37*t**5 + 4.79989746785454e+41*t**4 - 7.5013505384566e+45*t**3 + 1.87477623789514e+49*t**2 + 2.65887156850086e+52*t + 8.92288850651731e+54)/(2.31034485e+30*t**4 - 2.40880864037758e+42*t**3 + 1.80058335444066e+46*t**2 - 9.17890005233398e+49*t + 2.83920680016306e+52)']
G1 += ['-(3.34791791136009e+26*t**6 - 6.60684270736536e+38*t**5 + 8.17883655335588e+42*t**4 - 3.19817913274723e+46*t**3 + 4.59314449001853e+49*t**2 - 1.19790650269856e+52*t + 1.34987072685082e+55)/(3.13509075000008e+30*t**4 - 7.24370000072589e+42*t**3 + 4.81810608215637e+46*t**2 - 1.06153522314956e+50*t + 4.55150681183873e+52)']
G1 += ['-(2.67828076454869e+27*t**6 + 1.72399092689077e+39*t**5 - 2.15643954508537e+43*t**4 + 8.06652228914031e+46*t**3 - 1.03073887208476e+50*t**2 - 4.84415433019596e+52*t + 8.02500375048391e+55)/(2.73899587500007e+31*t**4 + 2.43465854658596e+43*t**3 - 1.52487220886188e+47*t**2 + 3.81410936035141e+50*t - 2.60884396450509e+53)']
G1 += ['(1.33925420692803e+32*t**6 - 1.97494512734861e+43*t**5 + 3.6106021424163e+47*t**4 - 1.828316148734e+51*t**3 + 3.26110643549735e+54*t**2 + 1.82082763741913e+57*t + 3.723533626347e+60)/(-1.25416285500003e+36*t**4 + 5.89833672656146e+47*t**3 - 3.31948552235508e+51*t**2 + 1.20232606670477e+55*t + 5.46226136382384e+56)']
G1 += ['-(8.3025043200002e+28*t**6 - 4.09496400409861e+45*t**5 + 4.78906834870265e+49*t**4 - 1.69508629677763e+53*t**3 + 1.98884913210989e+56*t**2 + 7.05924247690146e+58*t - 1.33233874574735e+62)/(9.6690000000002e+32*t**4 - 5.03774740512195e+49*t**3 + 3.05228594696852e+53*t**2 - 6.77992169654561e+56*t + 4.1183544135254e+59)']
G1 += ['-(4.0173408000001e+26*t**6 + 7.64656557950775e+42*t**5 - 1.4284742088641e+47*t**4 + 7.78342967953693e+50*t**3 - 1.23623876860731e+54*t**2 - 5.52768729504878e+56*t + 1.36469271317301e+60)/(4.5012000000001e+30*t**4 + 1.40812629743911e+47*t**3 - 1.3474870265158e+51*t**2 + 4.31467415172731e+54*t - 3.42012779323738e+57)']

G2 = []

G2 += ['-(2.53474459288799e+28*t**6 + 1.30883565097044e+41*t**5 - 6.6288735559448e+44*t**4 + 7.02856038007321e+47*t**3 + 3.13776699476978e+48*t**2 - 4.64281124332679e+53*t + 3.03346550161732e+56)/(1.12311657999999e+32*t**4 + 3.95794602838162e+44*t**3 - 8.05845004334485e+47*t**2 + 1.15237131131621e+51*t - 7.67406929796762e+53)']
G2 += ['(4.05627671203197e+31*t**6 + 1.35132495896729e+44*t**5 - 7.81402438703678e+47*t**4 + 2.39078892751322e+51*t**3 - 5.22724640522732e+54*t**2 + 4.55354850407033e+57*t + 2.27043571303493e+58)/(-1.79812443999998e+35*t**4 + 9.65566758025074e+47*t**3 - 4.39067769669292e+51*t**2 + 4.07368894701665e+54*t + 8.06323831414802e+56)']
G2 += ['2.0e-12*(5.00010035656547e+39*t**5 - 2.86234319806449e+43*t**4 + 1.06855562567269e+47*t**3 - 2.96148914490866e+50*t**2 + 3.4277819403489e+53*t - 9.10764097042482e+55)/(3.81232340000001e+19*t**4 + 1.14756840859728e+32*t**3 - 5.54112775194126e+35*t**2 + 6.84717417375297e+38*t - 1.41796461461882e+41)']
G2 += ['(6.08310719985698e+26*t**6 - 4.47105655616194e+43*t**5 + 1.98784896728034e+47*t**4 - 3.75556751944552e+49*t**3 - 4.36651841333891e+53*t**2 + 5.31173809401839e+56*t + 1.65657212868537e+59)/(-2.38286016000001e+35*t**4 + 2.40163851993312e+47*t**3 - 6.51756700642089e+50*t**2 + 7.59972940126176e+53*t + 1.49808140733211e+56)']
G2 += ['-(2.02770240004765e+26*t**6 + 1.0968031505479e+42*t**5 + 4.83618825223331e+45*t**4 - 9.40316402075237e+49*t**3 + 3.60114275857151e+53*t**2 - 5.88422216694954e+56*t + 2.04646165256384e+59)/(2.38328054000001e+34*t**4 + 6.63513905486217e+46*t**3 - 3.53591219245048e+50*t**2 + 6.29269220808437e+53*t - 1.92719737519738e+56)']
G2 += ['1.25e-12*(2.02770239999999e+23*t**6 - 3.66480929790933e+37*t**5 + 2.00038058325962e+43*t**4 - 2.13041288405242e+47*t**3 + 8.26763557217459e+50*t**2 - 1.38681940532649e+54*t + 5.45463053545959e+56)/(1.55572500000001e+16*t**4 - 1.80496264022074e+32*t**3 + 1.01878263847013e+36*t**2 - 1.85333300129126e+39*t + 6.67592585116653e+41)']
G2 += ['-(8.11040405951996e+34*t**6 - 2.21094792834649e+47*t**5 + 8.97112392549912e+50*t**4 + 9.18362353698938e+53*t**3 - 8.27351551173678e+57*t**2 + 1.57414152047435e+61*t - 6.05470831214638e+63)/(3.59419975999996e+38*t**4 - 2.10679066200612e+51*t**3 + 9.92123806003217e+54*t**2 - 1.83772224114475e+58*t + 6.55016673357189e+60)']
G2 += ['(6.08310719999995e+31*t**6 + 1.15785243143883e+48*t**5 - 2.01822829403924e+52*t**4 + 1.24519470427318e+56*t**3 - 2.82661304572524e+59*t**2 + 2.32937382411074e+62*t + 5.33497750962513e+64)/(-2.22039999999997e+35*t**4 + 5.26533929284116e+52*t**3 - 1.6912427610371e+56*t**2 + 8.6030126554803e+58*t + 1.76384772481453e+62)']
G2 += ['1.0e-7*(4.05520202975998e+23*t**6 + 8.62795375372984e+35*t**5 + 3.36151653874922e+39*t**4 - 6.20285592329014e+43*t**3 + 1.75366717360724e+47*t**2 - 1.85914756044708e+50*t + 8.33609896497647e+50)/(2.96747032000004e+20*t**4 - 4.02322056337987e+33*t**3 + 1.42882619579487e+37*t**2 - 1.38411332231767e+40*t - 5.4567377066513e+42)']
"""

# 4. Hardcoded Intersection Functions.

G = []
G1 = []
G2 = []

G += ['-(1.02907253515921e+23*t**6 + 5.31369836881899e+35*t**5 - 3.8999628187391e+39*t**4 + 8.96879527225381e+42*t**3 - 8.44546981788519e+45*t**2 + 1.50189434734654e+48*t + 2.94251182433602e+51)/(5.95903676000005e+26*t**4 + 2.74442402708568e+39*t**3 - 1.11791022692127e+43*t**2 + 1.75351330443477e+46*t - 1.08777492380643e+49)']
G += ['-(4.11698576167202e+22*t**6 + 1.37154982430906e+35*t**5 - 1.10702456811311e+39*t**4 + 3.5267857030672e+42*t**3 - 5.59606881698965e+45*t**2 + 2.64340570434936e+48*t + 1.17713435085807e+51)/(2.38439420000002e+26*t**4 + 8.78799171977478e+37*t**3 - 8.62151048684832e+41*t**2 + 4.26564010551861e+45*t - 4.6905653576949e+48)']
G += ['1.0e-7*(1.26873383128982e+32*t**5 - 1.01948449126411e+36*t**4 + 3.45938823962012e+39*t**3 - 6.33523521001329e+42*t**2 + 4.19346127808539e+45*t + 5.01238433769654e+47)/(2.151731e+16*t**4 + 1.6311107024557e+28*t**3 - 5.26356611151697e+31*t**2 - 1.97953566316401e+35*t + 3.66445920552749e+38)']
G += ['-(6.1741511999355e+17*t**6 - 4.53797348838513e+34*t**5 + 3.00121669834727e+38*t**4 - 5.08556403674325e+41*t**3 + 1.54631653870367e+44*t**2 + 2.14066517831606e+47*t - 6.46051722341711e+48)/(1.07596044e+26*t**4 - 2.81769632676879e+38*t**3 + 9.881528674196e+41*t**2 - 1.08666540830647e+45*t + 1.46406847530319e+47)']
G += ['-(2.05805040002153e+17*t**6 + 1.11321866702591e+33*t**5 + 2.71735216736376e+36*t**4 - 7.6680393688116e+40*t**3 + 2.57230617427243e+44*t**2 - 3.02309799016516e+47*t + 3.16242514432002e+48)/(1.07620528e+25*t**4 + 3.42116973328559e+37*t**3 - 1.39897778140361e+41*t**2 + 1.31340023492712e+44*t + 1.36249694369895e+47)']
G += ['1.0e-7*(2.05805040000001e+17*t**6 - 3.71965937485873e+31*t**5 + 2.08246873372304e+37*t**4 - 1.9104458924902e+41*t**3 + 5.85063540666231e+44*t**2 - 6.94592212812361e+47*t + 3.6085136460727e+49)/(483359999999999.0*t**4 - 6.50577529492309e+30*t**3 + 2.9322386547884e+34*t**2 - 3.11399071137193e+37*t - 2.52079585588091e+40)']
G += ['(-2.05794749748002e+22*t**6 + 5.61009627425368e+34*t**5 - 3.44452012125147e+38*t**4 + 3.67162102846136e+41*t**3 + 8.09567773705194e+44*t**2 - 1.86325493519958e+48*t + 2.92805263303124e+50)/(1.19175748000001e+26*t**4 - 4.52098491989653e+38*t**3 + 1.87069782421074e+42*t**2 - 2.48125429398216e+45*t + 7.76677123194518e+46)']
G += ['1.0e-7*(1.44063536608431e+18*t**6 + 9.87669920260596e+33*t**5 - 4.40306334870863e+37*t**4 - 7.80830412575288e+40*t**3 + 5.28159835568447e+44*t**2 - 7.06496090692947e+47*t + 1.77448927671849e+49)/(4.3033808e+18*t**4 - 1.19591264108479e+31*t**3 + 4.69432298748775e+34*t**2 - 4.86440086402978e+37*t - 2.57395848009325e+40)']
G += ['1.0e-7*(1.85224553218411e+18*t**6 + 1.97481786465759e+34*t**5 - 1.6548666348237e+38*t**4 + 5.61993734602924e+41*t**3 - 7.5623092388509e+44*t**2 - 1.81393021220785e+47*t + 4.2514908907738e+50)/(8.60716392e+18*t**4 + 8.24377549037554e+29*t**3 + 2.63993783073588e+34*t**2 - 1.33886758478488e+38*t + 1.006039255693e+41)']
G += ['1.0e-7*(2.26385630075267e+18*t**6 + 5.7476358131235e+33*t**5 + 4.29754781313501e+37*t**4 - 1.02527127673072e+42*t**3 + 2.54595173711829e+45*t**2 + 6.24366668719428e+46*t - 1.15074220989719e+51)/(4.30375052e+19*t**4 - 6.7527876067783e+31*t**3 + 1.56352571474147e+35*t**2 + 1.87391744044417e+38*t - 2.45921054272895e+41)']
G += ['-(5.14533180504002e+21*t**6 - 1.01538922900938e+34*t**5 + 9.87310321341404e+37*t**4 - 3.19097369069936e+41*t**3 + 2.47212117564761e+44*t**2 + 4.36659864516696e+47*t - 4.5129867985723e+50)/(5.67038820000002e+25*t**4 - 6.26721154358012e+37*t**3 + 5.43091626148281e+41*t**2 - 1.38671517306398e+45*t + 9.67381793631623e+47)']
G += ['(1.02904578049863e+22*t**6 + 6.62389701482971e+33*t**5 - 6.44184708284543e+37*t**4 + 2.6227131346258e+41*t**3 - 4.55369292141767e+44*t**2 + 1.55503585879834e+47*t + 1.56688128441405e+50)/(-8.65085895000005e+25*t**4 + 2.25213156185819e+37*t**3 + 1.06360891080914e+40*t**2 - 3.93961186592996e+44*t + 4.76051706676594e+47)']
G += ['-(1.02913324764601e+24*t**6 - 1.51762200786383e+35*t**5 + 2.81100093358268e+39*t**4 - 1.93264083802111e+43*t**3 + 3.10415227346458e+46*t**2 + 2.36886094436373e+49*t - 2.70165525518223e+52)/(1.13404644000001e+28*t**4 + 7.75750830338166e+39*t**3 - 3.93186026537629e+42*t**2 - 7.4518019319288e+46*t + 5.64443582491974e+49)']
G += ['(-3.18997812000002e+20*t**6 + 1.57336209314509e+37*t**5 - 1.51029091054066e+41*t**4 + 5.39604862125874e+44*t**3 - 7.89005333993513e+47*t**2 + 1.73512149852079e+50*t + 3.24512305938231e+53)/(1.30960000000002e+24*t**4 - 3.32903248850493e+40*t**3 + 3.68763933630328e+44*t**2 - 1.18612802845519e+48*t + 1.01811112048704e+51)']
G += ['-(3.08707560000002e+18*t**6 + 5.87590826854935e+34*t**5 - 1.04445553168945e+39*t**4 + 6.028031931312e+42*t**3 - 1.24762997572977e+46*t**2 + 7.04550135557613e+48*t + 3.47428550582021e+51)/(1.68040000000001e+22*t**4 - 9.64303248850506e+38*t**3 + 8.59389336303243e+41*t**2 + 8.63593221544821e+45*t - 1.29599387951297e+49)']
G += ['-(2.05794749748001e+22*t**6 + 4.37854284278221e+34*t**5 + 3.46179923095784e+37*t**4 - 2.24368464790114e+42*t**3 + 6.51618471173132e+45*t**2 - 5.06307390902657e+48*t - 1.34487965843955e+51)/(1.1608028000001e+25*t**4 + 1.07554436156225e+39*t**3 - 2.85328813765206e+42*t**2 - 1.17643399615817e+45*t + 5.87737548921887e+48)']

G1 += ['-(2.53474459288799e+28*t**6 + 1.30883565097044e+41*t**5 - 6.6288735559448e+44*t**4 + 7.02856038007321e+47*t**3 + 3.13776699476978e+48*t**2 - 4.64281124332679e+53*t + 3.03346550161732e+56)/(1.12311657999999e+32*t**4 + 3.95794602838162e+44*t**3 - 8.05845004334485e+47*t**2 + 1.15237131131621e+51*t - 7.67406929796762e+53)']
G1 += ['(4.05627671203197e+31*t**6 + 1.35132495896729e+44*t**5 - 7.81402438703678e+47*t**4 + 2.39078892751322e+51*t**3 - 5.22724640522732e+54*t**2 + 4.55354850407033e+57*t + 2.27043571303493e+58)/(-1.79812443999998e+35*t**4 + 9.65566758025074e+47*t**3 - 4.39067769669292e+51*t**2 + 4.07368894701665e+54*t + 8.06323831414802e+56)']
G1 += ['2.0e-12*(5.00010035656547e+39*t**5 - 2.86234319806449e+43*t**4 + 1.06855562567269e+47*t**3 - 2.96148914490866e+50*t**2 + 3.4277819403489e+53*t - 9.10764097042482e+55)/(3.81232340000001e+19*t**4 + 1.14756840859728e+32*t**3 - 5.54112775194126e+35*t**2 + 6.84717417375297e+38*t - 1.41796461461882e+41)']
G1 += ['(6.08310719985698e+26*t**6 - 4.47105655616194e+43*t**5 + 1.98784896728034e+47*t**4 - 3.75556751944552e+49*t**3 - 4.36651841333891e+53*t**2 + 5.31173809401839e+56*t + 1.65657212868537e+59)/(-2.38286016000001e+35*t**4 + 2.40163851993312e+47*t**3 - 6.51756700642089e+50*t**2 + 7.59972940126176e+53*t + 1.49808140733211e+56)']
G1 += ['-(2.02770240004765e+26*t**6 + 1.0968031505479e+42*t**5 + 4.83618825223331e+45*t**4 - 9.40316402075237e+49*t**3 + 3.60114275857151e+53*t**2 - 5.88422216694954e+56*t + 2.04646165256384e+59)/(2.38328054000001e+34*t**4 + 6.63513905486217e+46*t**3 - 3.53591219245048e+50*t**2 + 6.29269220808437e+53*t - 1.92719737519738e+56)']
G1 += ['1.25e-12*(2.02770239999999e+23*t**6 - 3.66480929790933e+37*t**5 + 2.00038058325962e+43*t**4 - 2.13041288405242e+47*t**3 + 8.26763557217459e+50*t**2 - 1.38681940532649e+54*t + 5.45463053545959e+56)/(1.55572500000001e+16*t**4 - 1.80496264022074e+32*t**3 + 1.01878263847013e+36*t**2 - 1.85333300129126e+39*t + 6.67592585116653e+41)']
G1 += ['-(8.11040405951996e+34*t**6 - 2.21094792834649e+47*t**5 + 8.97112392549912e+50*t**4 + 9.18362353698938e+53*t**3 - 8.27351551173678e+57*t**2 + 1.57414152047435e+61*t - 6.05470831214638e+63)/(3.59419975999996e+38*t**4 - 2.10679066200612e+51*t**3 + 9.92123806003217e+54*t**2 - 1.83772224114475e+58*t + 6.55016673357189e+60)']
G1 += ['(6.08310719999995e+31*t**6 + 1.15785243143883e+48*t**5 - 2.01822829403924e+52*t**4 + 1.24519470427318e+56*t**3 - 2.82661304572524e+59*t**2 + 2.32937382411074e+62*t + 5.33497750962513e+64)/(-2.22039999999997e+35*t**4 + 5.26533929284116e+52*t**3 - 1.6912427610371e+56*t**2 + 8.6030126554803e+58*t + 1.76384772481453e+62)']
G1 += ['1.0e-7*(4.05520202975998e+23*t**6 + 8.62795375372984e+35*t**5 + 3.36151653874922e+39*t**4 - 6.20285592329014e+43*t**3 + 1.75366717360724e+47*t**2 - 1.85914756044708e+50*t + 8.33609896497647e+50)/(2.96747032000004e+20*t**4 - 4.02322056337987e+33*t**3 + 1.42882619579487e+37*t**2 - 1.38411332231767e+40*t - 5.4567377066513e+42)']

G2 += ['(6.69523322160016e+23*t**6 - 1.82516332588575e+36*t**5 + 1.62404654495608e+40*t**4 - 3.06355229394846e+43*t**3 + 5.05023692601854e+45*t**2 - 5.88341253093106e+48*t + 5.03440788156712e+52)/(-7.42482510000016e+27*t**4 + 1.88749659238889e+40*t**3 - 6.30543066706728e+43*t**2 + 1.84101492551236e+46*t + 7.4110312937703e+49)']
G2 += ['-(9.37379501519099e+26*t**6 + 6.42648121034183e+42*t**5 - 4.6375415139244e+46*t**4 + 1.58132656550171e+49*t**3 + 1.50582793103161e+53*t**2 + 1.08399806417264e+56*t - 5.01172390411485e+59)/(9.250857e+33*t**4 + 5.78725944496901e+46*t**3 - 5.92100201171746e+49*t**2 - 5.55237089287194e+53*t + 9.43303486454366e+56)']
G2 += ['-(3.76625688448392e+22*t**6 + 4.01548939842799e+38*t**5 - 4.45639801376339e+42*t**4 + 1.39140669836403e+46*t**3 - 1.50392028589214e+49*t**2 - 7.69471149616197e+51*t + 1.04182112797364e+54)/(5.779335375e+29*t**4 + 5.27560960184084e+42*t**3 - 2.70381865724163e+46*t**2 + 5.68914236034823e+49*t - 2.31788697296422e+52)']
G2 += ['-(3.6825619380255e+22*t**6 + 9.34954907536971e+37*t**5 + 4.79989746785453e+41*t**4 - 7.50135053845659e+45*t**3 + 1.87477623789514e+49*t**2 + 2.65887156850087e+52*t + 8.92288850651726e+54)/(2.31034485e+30*t**4 - 2.40880864037758e+42*t**3 + 1.80058335444066e+46*t**2 - 9.17890005233398e+49*t + 2.83920680016306e+52)']
G2 += ['-(3.34791791136008e+26*t**6 - 6.60684270736536e+38*t**5 + 8.17883655335588e+42*t**4 - 3.19817913274722e+46*t**3 + 4.59314449001852e+49*t**2 - 1.19790650269854e+52*t + 1.34987072685081e+55)/(3.13509075000008e+30*t**4 - 7.24370000072589e+42*t**3 + 4.81810608215637e+46*t**2 - 1.06153522314956e+50*t + 4.55150681183873e+52)']
G2 += ['-(6.69570191137172e+30*t**6 + 4.30997731722693e+42*t**5 - 5.39109886271343e+46*t**4 + 2.01663057228508e+50*t**3 - 2.57684718021191e+53*t**2 - 1.21103858254899e+56*t + 2.00625093762098e+59)/(6.84748968750017e+34*t**4 + 6.0866463664649e+46*t**3 - 3.81218052215469e+50*t**2 + 9.53527340087854e+53*t - 6.52210991126273e+56)']
G2 += ['(2.67850841385607e+31*t**6 - 3.94989025469722e+42*t**5 + 7.2212042848326e+46*t**4 - 3.656632297468e+50*t**3 + 6.52221287099469e+53*t**2 + 3.64165527483827e+56*t + 7.44706725269399e+59)/(-2.50832571000007e+35*t**4 + 1.17966734531229e+47*t**3 - 6.63897104471017e+50*t**2 + 2.40465213340954e+54*t + 1.09245227276477e+56)']
G2 += ['-(2.07562608000005e+27*t**6 - 1.02374100102465e+44*t**5 + 1.19726708717566e+48*t**4 - 4.23771574194408e+51*t**3 + 4.97212283027473e+54*t**2 + 1.76481061922537e+57*t - 3.33084686436838e+60)/(2.41725000000005e+31*t**4 - 1.25943685128049e+48*t**3 + 7.6307148674213e+51*t**2 - 1.6949804241364e+55*t + 1.02958860338135e+58)']
G2 += ['-(2.00867040000005e+27*t**6 + 3.82328278975387e+43*t**5 - 7.14237104432051e+47*t**4 + 3.89171483976846e+51*t**3 - 6.18119384303654e+54*t**2 - 2.76384364752441e+57*t + 6.82346356586506e+60)/(2.25060000000005e+31*t**4 + 7.04063148719556e+47*t**3 - 6.73743513257898e+51*t**2 + 2.15733707586366e+55*t - 1.71006389661869e+58)']

# >>>

# 5. Register I. Functions

"""
i = 0
for f in G:
    exec 'def get_x' + str(i) + '(t): return ' + f
    i += 1

i = 0
for f in G1:
    exec 'def get_xx' + str(i) + '(t): return ' + f
    i += 1

i = 0
for f in G2:
    exec 'def get_xxx' + str(i) + '(t): return ' + f
    i += 1
"""
# >>>

"""
while i < N:
    f = globals()["get_xx%s" % i]
    print(f(t))
    i += 1

sys.exit()
"""

x1 = 695.86
y1 = 589.19

x2 = 806.89
y2 = 654.29

x3 = 866.77
y3 = 758.36

x4 = 745.27
y4 = 511.29

x5 = 878.40
y5 = 601.39

x6 = 938.86
y6 = 706.62

"""
1-2
2-3
3-1
POLYGON ((695.86 589.1900000000001, 745.27 511.29, 747.3 568.25, 695.86 589.1900000000001));
POLYGON ((806.89 654.29, 878.4 601.39, 858.05 652.84, 806.89 654.29));
POLYGON ((866.77 758.36, 938.86 706.62, 919.96 761.55, 866.77 758.36));
"""


"""
print(p_wkt)
print(q_wkt)
print(LineString([(x1, y1), (x4, y4)]))
print(LineString([(x2, y2), (x5, y5)]))
print(LineString([(x3, y3), (x6, y6)]))
sys.exit()
"""

#unit = [[[x1, y1, x2, y2, x3, y3], [x4, y4, x5, y5, x6, y6], interval.begin(), interval.end()], [interval.begin(), interval.end()]]
#units = [unit]

#ms1 = create_moving_segment2([], pass_through_control_points, units)

MS = []
for ms in reg_m_segs:
    MS += [create_moving_segment([ms], pass_through_control_points)]

TRIMS = []
for ms in tri_m_segs:
    TRIMS += [create_moving_segment([ms], pass_through_control_points)]

# >>>

unit = [[[x1, y1, x2, y2, x3, y3], interval.begin(), interval.end()], [interval.begin(), interval.end()]]
units = [unit]

mpoint1 = create_moving_point10(units)

unit = [[[x4, y4, x5, y5, x6, y6], interval.begin(), interval.end()], [interval.begin(), interval.end()]]
units = [unit]

mpoint2 = create_moving_point10(units)

# Moving Seg 2

x10 = 695.86
y10 = 589.19

x20 = 806.89
y20 = 654.29

x30 = 866.77
y30 = 758.36

x40 = 747.30
y40 = 568.25

x50 = 858.05
y50 = 652.84

x60 = 919.96
y60 = 761.55

#unit = [[[x10, y10, x20, y20, x30, y30], [x40, y40, x50, y50, x60, y60], interval.begin(), interval.end()], [interval.begin(), interval.end()]]
#units = [unit]

#ms2 = create_moving_segment2([], pass_through_control_points, units)

unit = [[[x40, y40, x50, y50, x60, y60], interval.begin(), interval.end()], [interval.begin(), interval.end()]]
units = [unit]

mpoint3 = create_moving_point10(units)

# Moving Seg 3
"""
x11 = 745.27
y11 = 511.29

x21 = 878.40
y21 = 601.39

x31 = 938.86
y31 = 706.62

x41 = 747.30
y41 = 568.25

x51 = 858.05
y51 = 652.84

x61 = 919.96
y61 = 761.55

unit = [[[x11, y11, x21, y21, x31, y31], [x41, y41, x51, y51, x61, y61], interval.begin(), interval.end()], [interval.begin(), interval.end()]]
units = [unit]
"""

#ms3 = create_moving_segment2([], pass_through_control_points, units)

#unit = [[[x41, y41, x51, y51, x61, y61], interval.begin(), interval.end()], [interval.begin(), interval.end()]]
#units = [unit]

#mpoint4 = create_moving_point10(units)

# M Points Intersection with th M Reg.

#p = loads(p_wkt)
#q = loads(q_wkt)

ipoint = shapely.geometry.Point(x1, y1)
fpoint = shapely.geometry.Point(x3, y3)

mp1_i_state, mp1_f_state = get_states_mp_mr(p, q, ipoint, fpoint)

i1 = get_mr_mp_intersections2(MS, mpoint1, mp1_i_state, mp1_f_state, 1, True)

ipoint = shapely.geometry.Point(x4, y4)
fpoint = shapely.geometry.Point(x6, y6)

mp2_i_state, mp2_f_state = get_states_mp_mr(p, q, ipoint, fpoint)

i2 = get_mr_mp_intersections2(MS, mpoint2, mp2_i_state, mp2_f_state, 1, True)

ipoint = shapely.geometry.Point(x40, y40)
fpoint = shapely.geometry.Point(x60, y60)

mp3_i_state, mp3_f_state = get_states_mp_mr(p, q, ipoint, fpoint)

i3 = get_mr_mp_intersections2(MS, mpoint3, mp3_i_state, mp3_f_state, 1, True)

# >>>>>>>>>>>>>>>

"""
ipoint = shapely.geometry.Point(x41, y41)
fpoint = shapely.geometry.Point(x61, y61)

mp4_i_state, mp4_f_state = get_states_mp_mr(p, q, ipoint, fpoint)

i4 = get_mr_mp_intersections2(MS, mpoint4, mp4_i_state, mp4_f_state, 1, True)
"""

#print(mp1_i_state, mp1_f_state, mp2_i_state, mp2_f_state)
#print(len(i1), len(i2))

"""
print('')
for i in i1:
    if isinstance(i, Interval):
        print(i.to_string())
    else:
        print(i)

print('')
for i in i2:
    if isinstance(i, Interval):
        print(i.to_string())
    else:
        print(i)

print('')
for i in i3:
    if isinstance(i, Interval):
        print(i.to_string())
    else:
        print(i)

sys.exit()
"""

#F = []
"""
M = []
I = []

for ms in MS:
    mms1 = LineString([(x1, y1), (x4, y4)])
    mms2 = ms.obj_at(interval.begin())
    mms3 = LineString([(x3, y3), (x6, y6)])
    mms4 = ms.obj_at(interval.end())

    initial_state, final_state = get_ms_states(mms1, mms2, mms3, mms4)

    #operation = 1
    intersections = get_ms_ms_intersections([ms], [ms1], initial_state, final_state, 1)

    if intersections != None and len(intersections) > 0:
        M += [ms, ms1]
        I += [intersections]
"""

#temp = [MS[30], MS[31], MS[32], MS[33]]

"""
F = []
intersections = None

for ms0 in MS:
    for ms1 in msegs1:
        intersections, intersection = get_msegs_intersections2(ms0, ms1, interval, intersections)

        mms1 = ms1.obj_at(interval.begin())
        mms2 = ms0.obj_at(interval.begin())
        mms3 = ms1.obj_at(interval.end())
        mms4 = ms0.obj_at(interval.end())

        initial_state, final_state = get_ms_states(mms1, mms2, mms3, mms4)

        if intersection != None and len(intersection) > 0:

            t = Symbol('t')
            x = Symbol('x')

            msu1 = ms.units[0]
            msu2 = ms1.units[0]

            T = (t - msu1.i.x) / (msu1.i.y - msu1.i.x)

            Ax, Ay = msu1.c0.curves[0].at(T)
            Bx, By = msu1.c1.curves[0].at(T)

            Cx, Cy = msu2.c0.curves[0].at(T)
            Dx, Dy = msu2.c1.curves[0].at(T)

            m1 = (By - Ay) / (Bx - Ax)
            m2 = (Dy - Cy) / (Dx - Cx)

            b1 = Ay - m1 * Ax
            b2 = Cy - m2 * Cx

            g = (m1 * x + (Ay - m1 * Ax)) - (m2 * x + (Cy - m2 * Cx))

            r = solve(g, x, t, dict=True)

            F += [str(r[0].get(x))]
"""

"""
G1 = get_F(MS, ms1, interval)
print('')
print('-------------')
for g in G1:
    print(g)
print('-------------')
sys.exit()
"""

"""
G1 = get_F(MS, ms1, interval)
G2 = get_F(MS, ms2, interval)
G3 = get_F(MS, ms3, interval)

print('')
print('-------------')
for g in G1:
    print(g)
print('-------------')
for g in G2:
    print(g)
print('-------------')
for g in G3:
    print(g)
print('')
"""
#sys.exit()

"""
TODOS
	calcular initial_state e final_state
	juntar intersectionx
	output 3 segs
"""


if_begin_exec_time = time.time()

if TESTING == 1:
    FIND_INT_FUNC = False
    PRINT_TEST_INFO = True
elif TESTING == 2:
    FIND_INT_FUNC = True
    PRINT_TEST_INFO = True
else:
    FIND_INT_FUNC = False
    PRINT_TEST_INFO = False

if FIND_INT_FUNC:
    ms1 = TRIMS[0]
    ms2 = TRIMS[1]
    ms3 = TRIMS[2]

    G = get_F(MS, ms1, interval)
    G1 = get_F(MS, ms2, interval)
    G2 = get_F(MS, ms3, interval)

# X. Register I. Functions

i = 0
for f in G:
    exec 'def get_x' + str(i) + '(t): return ' + f
    i += 1

i = 0
for f in G1:
    exec 'def get_xx' + str(i) + '(t): return ' + f
    i += 1

i = 0
for f in G2:
    exec 'def get_xxx' + str(i) + '(t): return ' + f
    i += 1

if_end_exec_time = time.time()

"""
print('')
print('-------------')
for g in G1:
    print(g)
print('-------------')
for g in G2:
    print(g)
print('-------------')
for g in G3:
    print(g)
print('')
sys.exit()
"""

ms1 = TRIMS[0]
ms2 = TRIMS[1]
ms3 = TRIMS[2]

reg_dict = {}

#intersections, M, I = get_ms_ms_intersections2(temp, [ms1], initial_state, final_state, 1)
intersections, M, I, IDICT = get_ms_ms_intersections2(MS, [ms1], initial_state, final_state, 1, 0, reg_dict)
intersections1, M1, I1, IDICT1 = get_ms_ms_intersections2(MS, [ms2], initial_state, final_state, 1, 1, reg_dict)
intersections2, M2, I2, IDICT2 = get_ms_ms_intersections2(MS, [ms3], initial_state, final_state, 1, 2, reg_dict)

"""
print(type(IDICT))

print(IDICT.get(0))
print(IDICT.items())
print(IDICT.keys())
print(IDICT.values())

#d1.update(d2)

for x in IDICT:
    print(x)
"""

"""
for x in IDICT:
    print(IDICT[x])

print('')

for x in reg_dict:
    print(reg_dict[x])
"""

"""
if 1 in IDICT:
    print('true')
else:
    print('false')
"""

#sys.exit()

"""
print('')
for _i in intersections:
    if isinstance(_i, Interval):
        print(_i.to_string())
    else:
        print(_i)
print('--------------')
for _i in intersections1:
    if isinstance(_i, Interval):
        print(_i.to_string())
    else:
        print(_i)
print('--------------')
for _i in intersections2:
    if isinstance(_i, Interval):
        print(_i.to_string())
    else:
        print(_i)
"""

#num_seg_int = len(intersections) + len(intersections1) + len(intersections2)
num_seg_int = len(I) + len(I1) + len(I2)

intersections = intersect_periods(intersections, intersections1)
intersections = intersect_periods(intersections, intersections2)

num_int_periods = len(intersections)
"""
for it in intersections:
    print(it.to_string())

sys.exit()
"""
"""
print('--------------')
for _i in intersections:
    if isinstance(_i, Interval):
        print(_i.to_string())
    else:
        print(_i)

sys.exit()
"""

"""
print('')

for i in I:
    print('')
    for it in i:
        if isinstance(it, Interval):
            print(it.to_string())
        else:
            print(it)

    print('>>')

print('')

for i in intersections:
    if isinstance(i, Interval):
        print(i.to_string())
    else:
        print(i)
"""

#print(len(intersections), len(M), len(I))
#sys.exit()

#get_samples_for_out4(MS, G, M, I, ms1, interval, n_samples, intersections, i1, i2, mpoint1, mpoint2)
#get_samples_for_out5(MS, G, G1, G2, M, M1, M2, I, I1, I2, ms1, ms2, ms3, interval, n_samples, intersections, i1, i2, i3, mpoint1, mpoint2, mpoint3)
#get_samples_for_out6(MS, G, G1, G2, M, M1, M2, I, I1, I2, ms1, ms2, ms3, interval, n_samples, intersections, i1, i2, i3, mpoint1, mpoint2, mpoint3)

proc_end_exec_time, n_invalid_geoms, n_complex_geoms, nu = get_samples_for_out7(MS, G, G1, G2, M, M1, M2, I, I1, I2, ms1, ms2, ms3, interval, n_samples, intersections, i1, i2, i3, mpoint1, mpoint2, mpoint3, reg_dict, IDICT, IDICT1, IDICT2)
#get_samples_for_out8(MS, G, G1, G2, M, M1, M2, I, I1, I2, ms1, ms2, ms3, interval, n_samples, intersections, i1, i2, i3, mpoint1, mpoint2, mpoint3, reg_dict, IDICT, IDICT1, IDICT2)

# >>>

if print_intersection_information:
    print('Intersection: IG: ' + str(n_invalid_geoms) + ', CG: ' + str(n_complex_geoms))

proc_exec_time = proc_end_exec_time - proc_begin_exec_time
if_exec_time = if_end_exec_time - if_begin_exec_time

day, hour, minutes, seconds = seconds_to_time(int(proc_exec_time))
iday, ihour, iminutes, iseconds = seconds_to_time(int(if_exec_time))

n_functions = len(G) + len(G1) + len(G2)
out = 'Exec. Time: ' + '{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0)
out += ', ' + 'Solver Exec. Time: ' + '{:0>2}'.format(ihour, precision_0) + ':' + '{:0>2}'.format(iminutes, precision_0) + ':' + '{:0>2}'.format(iseconds, precision_0)
out += ', NF: ' + str(n_functions)
out += ', IFETAVG: ' + format((if_exec_time * 100) / proc_exec_time, precision) + '%'
out += ', NU: ' + str(nu)

if print_solver_execution_time and TESTING == 0:
    print(out)

if PRINT_TEST_INFO:
    n_p = len(p.exterior.coords) - 1
    n_q = len(q.exterior.coords) - 1
    n_t = len(tri_1.exterior.coords) - 1

    proc_exec_time = proc_end_exec_time - proc_begin_exec_time
    if_exec_time = if_end_exec_time - if_begin_exec_time

    n_functions = len(G) + len(G1) + len(G2)

    #print('')
    #print('DEBUG')
    #print('')

    print('N Vertices in Reg 1: ' + str(n_p))
    print('N Vertices in Reg 2: ' + str(n_t))

    day, hour, minutes, seconds = seconds_to_time(int(proc_exec_time))
    print('Overall Exec. Time: ' + '{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0))

    day, hour, minutes, seconds = seconds_to_time(int(if_exec_time))
    print('Int. Functions Exec Time: ' + '{:0>2}'.format(hour, precision_0) + ':' + '{:0>2}'.format(minutes, precision_0) + ':' + '{:0>2}'.format(seconds, precision_0))

    print('Num F: ' + str(n_functions))
    #print('Num Inside Periods: ' + str(num_int_periods))
    print('Num Seg. Int: ' + str(num_seg_int))
    print('Num Int Units: ' + str(nu))

    if TESTING == 1:
        print('Int Functions Cached')
    else:
        print('Int Functions Not-Cached')

    #print('')
