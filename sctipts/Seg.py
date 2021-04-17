#from math import exp, expm1

import math

M_PI = 3.14159265358979323846
M_PI_OVER_2 = M_PI / 2

class Seg:

    def __init__(self, s = None, e = None):
        if s != None and e != None:
            self.valid = 1
        else:
            self.valid = 0
            
        self.s = s
        self.e = e
    
    """
     1.1 ~less-operator~ establishes a well-defined order of the segments,
     preferring lower-left points. This is mainly used to compare two lists of
     segments and finding and/or removing duplicates.
    """
    
    def __lt__(self, seg):
        if self.s.y < seg.s.y:
            return True
        elif self.s.y > seg.s.y:
            return False
        elif self.s.x < seg.s.x:
            return True
        elif self.s.x > seg.s.x:
            return False
        elif self.e.y < seg.e.y:
            return True
        elif self.e.y > seg.e.y:
            return False
        elif self.e.x < seg.e.x:
            return True
        elif self.e.x > seg.e.x:
            return False
        else:
            return False

    """
     1.2 ~ChangeDir~ changes the orientation of this segment
    """
    def change_dir(self):
        t = self.s
        self.s = self.e
        self.e = t

    """
     1.3 ~equality-operator~: Two segments are equal if their endpoints match.
    """
    
    """
    def equals(self, seg):
        return ((self.s == seg.s) and (self.e == seg.e))
    """
    
    def __eq__(self, seg): 
        if self.s == seg.s and self.e == seg.e: 
            return True
        else: 
            return False

    """
     1.4 ~angle~ calculates the angle of a Segment relative to the x-axis and
     returns it in degrees (0-360)
    """
    def angle(self):
        ret = 0
        dx = self.e.x - self.s.x
        dy = self.e.y - self.s.y

        if self.e.x == self.s.x:
            if self.e.y < self.s.y:
                ret = -M_PI_OVER_2
            else:
                ret = M_PI_OVER_2
            #ret = (self.e.y < self.s.y) ? -M_PI / 2 : M_PI / 2;
        else:
            ret = math.atan(dy / dx)

        ret = ret * 90.0 / M_PI_OVER_2
        
        if dx < 0:
            ret += 180
        elif dy < 0:
            ret += 360

        return ret

    """
     1.5 ~ToString~ generates a textual representation of this object for
     debugging purposes.
    """
    def to_string(self):
        return "Seg: " + self.s.to_string() + ' ' + self.e.to_string() + ' A: ' + self.angle()

    """
    // helper-function isOnLine checks, if the point b is on the Segment (a c) under
    // the precondition, that the three points a, b and c are collinear. Used by
    // Seg::intersects
    """
    def is_on_line(selg, a, b, c):
        return (b.x <= max(a.x, c.x) and 
                    b.x >= min(a.x, c.x) and
                    b.y <= max(a.y, c.y) and
                    b.y >= min(a.y, c.y))

    """
    // sign determines the order of the points a, b, c (clockwise, collinear or
    // counterclockwise)
    """
    def sign(self, a, b, c):
        s = (b.y - a.y) * (c.x - b.x) - (b.x - a.x) * (c.y - b.y)
        
        if s > 0:
            return 1
        elif s < 0:
            return -1
        else:
            return 0
        #return (s > 0) ? 1 : ((s < 0) ? -1 : 0)

    """
     1.6 ~intersects~ checks, if this segment intersects with segment a.
    """
    def intersects(self, seg):
        # If any segment is degenerated, it cannot intersect
        if (self.s == self.e) or (seg.s == seg.e):
            return False
        
        # The two segments completely overlap
        if (self == seg) or ((self.s == seg.s) and (self.e == seg.e)):
            return True
        
        # If they only touch in one point it is not considered an intersection
        if (self.e == seg.s) or (self.s == seg.e) or (self.s == seg.s) or (self.e == seg.e):
            return False
        
        s1 = self.sign(self.s, self.e, seg.s)
        s2 = self.sign(self.s, self.e, seg.e)
        s3 = self.sign(seg.s, seg.e, self.s)
        s4 = self.sign(seg.s, seg.e, self.e)

        # The segments intersect
        if s1 != s2 and s3 != s4:
            return True

        # One point of a segment is on the other segment, this is an intersection
        if (s1 == 0 and self.is_on_line(self.s, seg.s, self.e)) or \
           (s2 == 0 and self.is_on_line(self.s, seg.e, self.e)) or \
           (s3 == 0 and self.is_on_line(seg.s, self.s, seg.e)) or \
           (s4 == 0 and self.is_on_line(seg.s, self.e, seg.e)):
            return True

        # No intersection otherwise
        return False
