// Given an array of integers, it returns the sum. [1,3,3,2]->9

function Sum(xs: seq<int>): int {}

method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
{}
