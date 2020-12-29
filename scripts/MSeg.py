import numpy as np
from shapely.geometry import Point, Polygon, LineString, MultiPolygon
import shapely.wkt
from shapely.wkt import dumps, loads
import math
import sys

"""
    
    A Moving segment

"""

class MSeg:
    
    def __init__(self, i_ep_1, f_ep_1, i_ep_2, f_ep_2, starting_time = 0, ending_time = 1, final = False, reverse = 0):
        self.i_ep_1 = i_ep_1
        self.f_ep_1 = f_ep_1
        self.i_ep_2 = i_ep_2
        self.f_ep_2 = f_ep_2
        
        self.starting_time = float(starting_time)
        self.ending_time = float(ending_time)
        self.final = final
        self.reverse = reverse

    def set_val(self, val, idx):
        if idx == 0:
            self.i_ep_1 = val
        elif idx == 1:
            self.f_ep_1 = val
        elif idx == 2:
            self.i_ep_2 = val
        elif idx == 3:
            self.f_ep_2 = val

    def set_reverse(self, reverse):
        self.reverse = reverse
    
    def get_reverse(self):
        return self.reverse
    
    def rev(self):
        return (self.reverse == 2)
    
    def get_val(self, idx):
        if idx == 0:
            return self.i_ep_1
        elif idx == 1:
            return self.f_ep_1
        elif idx == 2:
            return self.i_ep_2
        elif idx == 3:
            return self.f_ep_2

    def at(self, t):
        if self.starting_time < 0 or self.ending_time > 1:
            return None, None, None, None
        
        #if t < self.starting_time:
        if t <= self.starting_time:
            return None, None, None, None
                
        if t > self.ending_time:
            if self.final:
                return self.i_ep_2.x, self.i_ep_2.y, self.f_ep_2.x, self.f_ep_2.y
            else:
                return None, None, None, None
            
        i_x = 0
        i_y = 0
        f_x = 0
        f_y = 0
            
        if self.starting_time == 0 and self.ending_time == 1:
            i_x = self.i_ep_1.x + t * (self.i_ep_2.x - self.i_ep_1.x)
            i_y = self.i_ep_1.y + t * (self.i_ep_2.y - self.i_ep_1.y)

            f_x = self.f_ep_1.x + t * (self.f_ep_2.x - self.f_ep_1.x)
            f_y = self.f_ep_1.y + t * (self.f_ep_2.y - self.f_ep_1.y)
        else:
            if self.starting_time != 0 and self.ending_time == 1:
                w1_n = (1 - t)
                w1_d = (1 - self.starting_time)
                    
                dt = float(w1_n) / w1_d
                t = float(t - self.starting_time) / w1_d

                i_x = dt * self.i_ep_1.x + t * (self.i_ep_2.x)
                i_y = dt * self.i_ep_1.y + t * (self.i_ep_2.y)

                f_x = dt * self.f_ep_1.x + t * (self.f_ep_2.x)
                f_y = dt * self.f_ep_1.y + t * (self.f_ep_2.y)
            elif self.starting_time == 0 and self.ending_time != 1:
                w1_n = (self.ending_time - t)
                w1_d = self.ending_time

                dt = float(w1_n) / w1_d
                t = float(t) / w1_d

                i_x = dt * self.i_ep_1.x + t * (self.i_ep_2.x)
                i_y = dt * self.i_ep_1.y + t * (self.i_ep_2.y)

                f_x = dt * self.f_ep_1.x + t * (self.f_ep_2.x)
                f_y = dt * self.f_ep_1.y + t * (self.f_ep_2.y)
            else:
                w1_n = (self.ending_time - t)
                w1_d = self.ending_time - self.starting_time

                dt = float(w1_n) / w1_d
                t = float(t - self.starting_time) / w1_d

                i_x = dt * self.i_ep_1.x + t * (self.i_ep_2.x)
                i_y = dt * self.i_ep_1.y + t * (self.i_ep_2.y)

                f_x = dt * self.f_ep_1.x + t * (self.f_ep_2.x)
                f_y = dt * self.f_ep_1.y + t * (self.f_ep_2.y)

        return i_x, i_y, f_x, f_y

    def at2(self, t):
        if self.starting_time < 0 or self.ending_time > 1:
            return None, None, None, None
        
        #if t < self.starting_time:
        if t < self.starting_time:
            return None, None, None, None
                
        if t > self.ending_time:
            if self.final:
                return self.i_ep_2.x, self.i_ep_2.y, self.f_ep_2.x, self.f_ep_2.y
            else:
                return None, None, None, None
            
        i_x = 0
        i_y = 0
        f_x = 0
        f_y = 0
            
        if self.starting_time == 0 and self.ending_time == 1:
            i_x = self.i_ep_1.x + t * (self.i_ep_2.x - self.i_ep_1.x)
            i_y = self.i_ep_1.y + t * (self.i_ep_2.y - self.i_ep_1.y)

            f_x = self.f_ep_1.x + t * (self.f_ep_2.x - self.f_ep_1.x)
            f_y = self.f_ep_1.y + t * (self.f_ep_2.y - self.f_ep_1.y)
        else:
            if self.starting_time != 0 and self.ending_time == 1:
                w1_n = (1 - t)
                w1_d = (1 - self.starting_time)
                    
                dt = float(w1_n) / w1_d
                t = float(t - self.starting_time) / w1_d

                i_x = dt * self.i_ep_1.x + t * (self.i_ep_2.x)
                i_y = dt * self.i_ep_1.y + t * (self.i_ep_2.y)

                f_x = dt * self.f_ep_1.x + t * (self.f_ep_2.x)
                f_y = dt * self.f_ep_1.y + t * (self.f_ep_2.y)
            elif self.starting_time == 0 and self.ending_time != 1:
                w1_n = (self.ending_time - t)
                w1_d = self.ending_time

                dt = float(w1_n) / w1_d
                t = float(t) / w1_d

                i_x = dt * self.i_ep_1.x + t * (self.i_ep_2.x)
                i_y = dt * self.i_ep_1.y + t * (self.i_ep_2.y)

                f_x = dt * self.f_ep_1.x + t * (self.f_ep_2.x)
                f_y = dt * self.f_ep_1.y + t * (self.f_ep_2.y)
            else:
                w1_n = (self.ending_time - t)
                w1_d = self.ending_time - self.starting_time

                dt = float(w1_n) / w1_d
                t = float(t - self.starting_time) / w1_d

                i_x = dt * self.i_ep_1.x + t * (self.i_ep_2.x)
                i_y = dt * self.i_ep_1.y + t * (self.i_ep_2.y)

                f_x = dt * self.f_ep_1.x + t * (self.f_ep_2.x)
                f_y = dt * self.f_ep_1.y + t * (self.f_ep_2.y)

        return i_x, i_y, f_x, f_y

    def get_time(self):
        return self.starting_time, self.ending_time
    
    def get_ipoint(self):
        return self.i_ep_1, self.f_ep_1
    
    def to_string(self):
        out = str(self.i_ep_1.x) + ' ' + str(self.i_ep_1.y) + ' ' + str(self.f_ep_1.x) + ' ' + str(self.f_ep_1.y) + ' '
        out += str(self.i_ep_2.x) + ' ' + str(self.i_ep_2.y) + ' ' + str(self.f_ep_2.x) + ' ' + str(self.f_ep_2.y) + ' '
        out += str(self.starting_time) + ' ' + str(self.ending_time) + ' ' + str(self.final)
        
        print(out)