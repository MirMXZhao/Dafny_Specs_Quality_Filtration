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
    def positive(s):
        def lambda0_(forall_var_0_):
            d_0_u_: int = forall_var_0_
            return not (((0) <= (d_0_u_)) and ((d_0_u_) < (len(s)))) or (((s)[d_0_u_]) >= (0))

        return _dafny.quantifier(_dafny.IntegerRange(0, len(s)), True, lambda0_)

    @staticmethod
    def CountEven(s):
        d_0___accumulator_ = 0
        while True:
            with _dafny.label():
                if (s) == (_dafny.SeqWithoutIsStrInference([])):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + ((1 if (_dafny.euclidian_modulus((s)[(len(s)) - (1)], 2)) == (0) else 0))
                    in0_ = _dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):])
                    s = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def mcountEven(v):
        n: int = int(0)
        n = 0
        d_0_i_: int
        d_0_i_ = 0
        while (d_0_i_) < ((v).length(0)):
            if (_dafny.euclidian_modulus((v)[d_0_i_], 2)) == (0):
                n = (n) + (1)
            d_0_i_ = (d_0_i_) + (1)
        return n

    @staticmethod
    def Main(noArgsParameter__):
        d_0_a_: _dafny.Array
        nw0_ = _dafny.Array(None, 5)
        nw0_[int(0)] = 2
        nw0_[int(1)] = 4
        nw0_[int(2)] = 3
        nw0_[int(3)] = 4
        nw0_[int(4)] = 1
        d_0_a_ = nw0_
        d_1_b_: _dafny.Array
        nw1_ = _dafny.Array(None, 10)
        nw1_[int(0)] = 2
        nw1_[int(1)] = 4
        nw1_[int(2)] = 3
        nw1_[int(3)] = 4
        nw1_[int(4)] = 1
        nw1_[int(5)] = 2
        nw1_[int(6)] = 1
        nw1_[int(7)] = 1000
        nw1_[int(8)] = 3004
        nw1_[int(9)] = 1283407
        d_1_b_ = nw1_
        d_2_a1_: int
        out0_: int
        out0_ = default__.mcountEven(d_0_a_)
        d_2_a1_ = out0_
        d_3_b1_: int
        out1_: int
        out1_ = default__.mcountEven(d_1_b_)
        d_3_b1_ = out1_
        print(out0_)
        print(out1_)

