method MedianOfThree(a: int, b: int, c: int) returns (median: int)
    ensures median == a || median == b || median == c
    ensures (median >= a && median <= b) || (median >= b && median <= a) || (median >= a && median <= c) || (median >= c && median <= a) || (median >= b && median <= c) || (median >= c && median <= b)
{}