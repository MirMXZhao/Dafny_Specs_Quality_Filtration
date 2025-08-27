method non_overlapping_intervals(intervals: array2<int>) returns (count: int)
    modifies intervals
    requires 1 <= intervals.Length0 <= 100000
    requires intervals.Length1 == 2
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
    ensures count >= 0
{}

method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
{}

predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{}

predicate partitioned(a: array2<int>, i: int)
    reads a
    requires a.Length1 == 2
{}