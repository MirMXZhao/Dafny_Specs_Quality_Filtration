function Sum(xs: seq<int>): int {}

method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
{}