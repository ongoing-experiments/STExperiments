import numpy as np
import random
import math
from math import sqrt

"""
    
    A Module with utils.
    
"""

def distance(x1, y1, x2, y2):    
    return sqrt((x2 - x1)**2 + (y2 - y1)**2)

"""

    Credits:
    https://stackoverflow.com/questions/28260962/calculating-angles-between-line-segments-python-with-math-atan2

"""
def dot(vA, vB):
    return vA[0]*vB[0]+vA[1]*vB[1]

def ang(lineA, lineB):
    # Get nicer vector form
    vA = [(lineA[0][0]-lineA[1][0]), (lineA[0][1]-lineA[1][1])]
    vB = [(lineB[0][0]-lineB[1][0]), (lineB[0][1]-lineB[1][1])]
    
    # Get dot prod
    dot_prod = dot(vA, vB)
    
    # Get magnitudes
    magA = dot(vA, vA)**0.5
    magB = dot(vB, vB)**0.5
    
    # Get cosine value
    cos_ = dot_prod/magA/magB
    
    # Get angle in radians and then convert to degrees
    angle = math.acos(dot_prod/magB / magA)
    
    # Basically doing angle <- angle mod 360
    ang_deg = math.degrees(angle) % 360

    if ang_deg-180 >= 0:
        # As in if statement
        return 360 - ang_deg
    else: 

        return ang_deg

"""

    Division by zero problem.

"""
def slope(x1, y1, x2, y2): # Line slope given two points:
    return (y2-y1)/(x2-x1)

def angle(s1, s2): 
    return math.degrees(math.atan((s2-s1)/(1+(s2*s1))))

def angle_between_two_lines(lineA, lineB):
    slope1 = slope(lineA[0][0], lineA[0][1], lineA[1][0], lineA[1][1])
    slope2 = slope(lineB[0][0], lineB[0][1], lineB[1][0], lineB[1][1])

    ang = angle(slope1, slope2)

def tests():
    lineA = ((0.6, 3.6), (1.6, 3))
    lineB = ((1.6, 3), (2, 3.6))
    
    # 45
    lineA = ((1, 1), (3, 3))
    lineB = ((1, 1), (1, 6))
    
    # 90
    #lineA = ((1, 1), (3, 3))
    #lineB = ((1, 1), (1, 6))


    #slope1 = slope(lineA[0][0], lineA[0][1], lineA[1][0], lineA[1][1])
    #slope2 = slope(lineB[0][0], lineB[0][1], lineB[1][0], lineB[1][1])

    #a = angle(slope1, slope2)
    #print('Angle in degrees = ', a)
    
    a = ang(lineA, lineB)
    print('Angle in degrees = ', a)

#tests()