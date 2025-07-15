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
    def AllElementsEqual(a, n):
        result: bool = False
        d_0_i_: int
        d_0_i_ = 0
        while (d_0_i_) < ((a).length(0)):
            if ((a)[d_0_i_]) != (n):
                result = False
                return result
            d_0_i_ = (d_0_i_) + (1)
        result = True
        return result

    @staticmethod
    def Main(noArgsParameter__):
        d_0_a_: _dafny.Array
        nw0_ = _dafny.Array(None, 3)
        nw0_[int(0)] = -3
        nw0_[int(1)] = -3
        nw0_[int(2)] = -3
        d_0_a_ = nw0_
        d_1_b_: _dafny.Array
        nw1_ = _dafny.Array(None, 2)
        nw1_[int(0)] = 2
        nw1_[int(1)] = 1
        d_1_b_ = nw1_
        d_2_c_: _dafny.Array
        nw2_ = _dafny.Array(None, 5)
        nw2_[int(0)] = 1
        nw2_[int(1)] = 1
        nw2_[int(2)] = 1
        nw2_[int(3)] = 1
        nw2_[int(4)] = 5
        d_2_c_ = nw2_
        d_3_a1_: bool
        out0_: bool
        out0_ = default__.AllElementsEqual(d_0_a_, -3)
        d_3_a1_ = out0_
        d_4_a1_k_: bool
        out1_: bool
        out1_ = default__.AllElementsEqual(d_0_a_, 4)
        d_4_a1_k_ = out1_
        d_5_b1_: bool
        out2_: bool
        out2_ = default__.AllElementsEqual(d_1_b_, 1)
        d_5_b1_ = out2_
        d_6_b1_k_: bool
        out3_: bool
        out3_ = default__.AllElementsEqual(d_1_b_, 3)
        d_6_b1_k_ = out3_
        d_7_c1_: bool
        out4_: bool
        out4_ = default__.AllElementsEqual(d_2_c_, 1)
        d_7_c1_ = out4_
        print(out0_)
        print(out1_)
        print(out2_)
        print(out3_)
        print(out4_)

