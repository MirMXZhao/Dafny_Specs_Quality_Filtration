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
    def FloorDivide(a, b):
        res: _dafny.Array = _dafny.Array(None, 0)
        nw0_ = _dafny.Array(int(0), (a).length(0))
        res = nw0_
        d_0_i_: int
        d_0_i_ = 0
        while (d_0_i_) < ((a).length(0)):
            (res)[(d_0_i_)] = _dafny.euclidian_division((a)[d_0_i_], (b)[d_0_i_])
            d_0_i_ = (d_0_i_) + (1)
        return res

    @staticmethod
    def Main(noArgsParameter__):
        d_0_a_: _dafny.Array
        nw0_ = _dafny.Array(None, 7)
        nw0_[int(0)] = 1
        nw0_[int(1)] = 3
        nw0_[int(2)] = 5
        nw0_[int(3)] = 8
        nw0_[int(4)] = 200
        nw0_[int(5)] = 50
        nw0_[int(6)] = 20
        d_0_a_ = nw0_
        d_1_b_: _dafny.Array
        nw1_ = _dafny.Array(None, 7)
        nw1_[int(0)] = 2
        nw1_[int(1)] = 2
        nw1_[int(2)] = 2
        nw1_[int(3)] = 3
        nw1_[int(4)] = 27
        nw1_[int(5)] = 12
        nw1_[int(6)] = 3
        d_1_b_ = nw1_
        d_2_c_: _dafny.Array
        out0_: _dafny.Array
        out0_ = default__.FloorDivide(d_0_a_, d_1_b_)
        d_2_c_ = out0_
        for i in range(7):
            print(out0_[i])

