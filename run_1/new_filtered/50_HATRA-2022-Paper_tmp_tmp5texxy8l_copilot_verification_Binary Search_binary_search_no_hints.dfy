method BinarySearch(arr: array<int>, target: int) returns (index: int)
    requires distinct(arr)
    requires sorted(arr)
    ensures -1 <= index < arr.Length
    ensures index == -1 ==> not_found(arr, target)
    ensures index != -1 ==> found(arr, target, index)
{}

predicate sorted(a: array<int>)
reads a
{}

predicate distinct(arr: array<int>)
    reads arr
{}

predicate not_found(arr: array<int>, target: int)
reads arr
{}

predicate found(arr: array<int>, target: int, index: int)
requires -1 <= index < arr.Length;
reads arr
{}