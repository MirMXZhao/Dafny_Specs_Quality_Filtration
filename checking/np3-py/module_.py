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
    def arange(start, stop, step):
        ret: _dafny.Array = _dafny.Array(None, 0)
        d_0_diff_: _dafny.BigRational
        d_0_diff_ = (stop) - (start)
        d_1_quotient_: _dafny.BigRational
        d_1_quotient_ = (d_0_diff_) / (step)
        d_2_length_: int
        d_2_length_ = (floor((d_1_quotient_))) + (1)
        nw0_ = _dafny.Array(_dafny.BigRational(), d_2_length_)
        ret = nw0_
        d_3_i_: int
        d_3_i_ = 0
        while (d_3_i_) < (d_2_length_):
            (ret)[(d_3_i_)] = (start) + ((_dafny.BigRational(d_3_i_, 1)) * (step))
            d_3_i_ = (d_3_i_) + (1)
        return ret

    @staticmethod
    def Main(noArgsParameter__):
        print("hello")
        d_0_b_: _dafny.Array
        out0_: _dafny.Array
        out0_ = default__.arange(_dafny.BigRational('1e0'), _dafny.BigRational('2e1'), _dafny.BigRational('2e0'))
        d_0_b_ = out0_
        print(out0_)
        for i in range(10):
            print(d_0_b_[i])

