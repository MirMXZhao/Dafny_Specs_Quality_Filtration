method DifferenceMinMax(a: array<int>) returns (diff: int)
    requires a.Length > 0
    ensures diff == (Max(a[..]) - Min(a[..]))
{}

function Min(a: seq<int>) : (m: int)
    requires |a| > 0
{}

function Max(a: seq<int>) : (m: int)
    requires |a| > 0
{}
