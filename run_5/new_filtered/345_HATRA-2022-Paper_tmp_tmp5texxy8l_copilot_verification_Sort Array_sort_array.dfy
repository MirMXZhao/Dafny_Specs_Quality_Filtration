method sortArray(arr: array<int>) returns (arr_sorted: array<int>)
    requires 0 <= arr.Length < 10000
    ensures sorted(arr_sorted, 0, arr_sorted.Length)
    ensures multiset(arr[..]) == multiset(arr_sorted[..])
    modifies arr
{} 

predicate sorted(arr: array<int>, start: int, end: int)
requires 0 <= start <= end <= arr.Length
reads arr
{}

predicate pivot(arr: array<int>, pivot: int)
requires 0 <= pivot <= arr.Length
reads arr
{}