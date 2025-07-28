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
    def min(s):
        if (len(s)) == (2):
            return default__.MinPair(s)
        elif True:
            return default__.MinPair(_dafny.SeqWithoutIsStrInference([(s)[0], default__.min(_dafny.SeqWithoutIsStrInference((s)[1::]))]))

    @staticmethod
    def MinPair(s):
        if ((s)[0]) <= ((s)[1]):
            return (s)[0]
        elif True:
            return (s)[1]

    @staticmethod
    def SecondSmallest(s):
        secondSmallest: int = int(0)
        d_0_minimum_: int
        d_0_minimum_ = default__.min(_dafny.SeqWithoutIsStrInference((s)[::]))
        d_1_candidate_: int
        d_1_candidate_ = (s)[0]
        d_2_i_: int
        d_2_i_ = 0
        while ((d_2_i_) < ((s).length(0))) and (((s)[d_2_i_]) == (d_0_minimum_)):
            d_2_i_ = (d_2_i_) + (1)
        if (d_2_i_) < ((s).length(0)):
            secondSmallest = (s)[d_2_i_]
        elif True:
            secondSmallest = (s)[0]
        d_2_i_ = 0
        while (d_2_i_) < ((s).length(0)):
            if (((s)[d_2_i_]) != (d_0_minimum_)) and (((s)[d_2_i_]) < (secondSmallest)):
                secondSmallest = (s)[d_2_i_]
            d_2_i_ = (d_2_i_) + (1)
        return secondSmallest

    @staticmethod
    def Main(noArgsParameter__):
        d_0_smallArr_: _dafny.Array
        nw0_ = _dafny.Array(None, 2)
        nw0_[int(0)] = 1
        nw0_[int(1)] = 2
        d_0_smallArr_ = nw0_
        out0 = default__.SecondSmallest(nw0_)
        d_1_bigArr1_: _dafny.Array
        nw1_ = _dafny.Array(None, 6)
        nw1_[int(0)] = 10
        nw1_[int(1)] = 8
        nw1_[int(2)] = 4
        nw1_[int(3)] = -100
        nw1_[int(4)] = -30
        nw1_[int(5)] = -39
        d_1_bigArr1_ = nw1_
        out1 = default__.SecondSmallest(nw1_)
        d_2_bigArr2_: _dafny.Array
        nw2_ = _dafny.Array(None, 8)
        nw2_[int(0)] = 100
        nw2_[int(1)] = 4
        nw2_[int(2)] = 60
        nw2_[int(3)] = 3
        nw2_[int(4)] = 53
        nw2_[int(5)] = 59
        nw2_[int(6)] = -5
        nw2_[int(7)] = 200
        d_2_bigArr2_ = nw2_
        out2 = default__.SecondSmallest(nw2_)
        d_3_bigArr3_: _dafny.Array
        nw3_ = _dafny.Array(None, 6)
        nw3_[int(0)] = 1
        nw3_[int(1)] = 1
        nw3_[int(2)] = 2
        nw3_[int(3)] = 3
        nw3_[int(4)] = 6
        nw3_[int(5)] = 10
        d_3_bigArr3_ = nw3_
        out3 = default__.SecondSmallest(nw3_)
        print(out0)
        print(out1)
        print(out2)
        print(out3)


