import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: module_

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def factImp(n):
        r: int = int(0)
        if (n) <= (1):
            r = 1
        elif True:
            d_0_i_: int
            d_0_i_ = 1
            r = 1
            while (d_0_i_) <= (n):
                r = (r) * (d_0_i_)
                d_0_i_ = (d_0_i_) + (1)
        return r

    @staticmethod
    def Main(noArgsParameter__):
        d_0_a_: int
        out0_: int
        out0_ = default__.factImp(5)
        d_0_a_ = out0_
        d_1_b_: int
        out1_: int
        out1_ = default__.factImp(4)
        d_1_b_ = out1_
        print(out0_)
        print(out1_)

