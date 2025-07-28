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
    def mroot2(n):
        r: int = int(0)
        r = 0
        while (((r) + (1)) * ((r) + (1))) <= (n):
            r = (r) + (1)
        return r

    @staticmethod
    def Main(noArgsParameter__):
        d_0_a_: int
        out0_: int
        out0_ = default__.mroot2(25)
        d_0_a_ = out0_
        d_1_b_: int
        out1_: int
        out1_ = default__.mroot2(82)
        d_1_b_ = out1_
        d_2_c_: int
        out2_: int
        out2_ = default__.mroot2(250)
        d_2_c_ = out2_
        print(out0_, out1_, out2_)

