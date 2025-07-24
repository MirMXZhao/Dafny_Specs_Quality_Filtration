function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    reads a;
    {}

    method SumInRange(a: array<int>, start: int, end: int) returns (sum: int)
    requires a != null
    requires 0 <= start && start <= end && end <= a.Length
    ensures sum == sumTo(a, start, end)
    {}