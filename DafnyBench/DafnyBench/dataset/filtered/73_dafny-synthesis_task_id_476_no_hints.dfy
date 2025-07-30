method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
{}

function Min(a: seq<int>) : int
    requires |a| > 0
{}

function Max(a: seq<int>) : int
    requires |a| > 0
{}