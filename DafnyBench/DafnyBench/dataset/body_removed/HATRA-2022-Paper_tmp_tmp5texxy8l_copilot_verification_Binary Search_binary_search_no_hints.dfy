// Dafny verification of binary search alogirthm from binary_search.py
// Inspired by: https://ece.uwaterloo.ca/~agurfink/stqam/rise4fun-Dafny/#h211

method BinarySearch(arr: array<int>, target: int) returns (index: int)
    requires distinct(arr)
    requires sorted(arr)
    ensures -1 <= index < arr.Length
    ensures index == -1 ==> not_found(arr, target)
    ensures index != -1 ==> found(arr, target, index)
{}

// Predicate to check that the array is sorted
predicate sorted(a: array<int>)
reads a
{}

// Predicate to that each element is unique
predicate distinct(arr: array<int>)
    reads arr
{}

// Predicate to that the target is not in the array
predicate not_found(arr: array<int>, target: int)
reads arr
{}

// Predicate to that the target is in the array
predicate found(arr: array<int>, target: int, index: int)
requires -1 <= index < arr.Length;
reads arr
{}



