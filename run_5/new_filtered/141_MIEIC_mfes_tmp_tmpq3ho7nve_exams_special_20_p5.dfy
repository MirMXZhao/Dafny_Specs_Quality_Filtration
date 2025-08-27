type T = int
predicate sorted(a: array<T>, n: nat) 
    requires n <= a.Length
    reads a
{}

// Use binary search to find an appropriate position to insert a value 'x'
// in a sorted array 'a', so that it remains sorted.
method binarySearch(a: array<T>, x: T) returns (index: int) 
    requires sorted(a, a.Length)
    ensures sorted(a, a.Length)
    ensures 0 <= index <= a.Length
    ensures index > 0 ==> a[index-1] <= x
    ensures index < a.Length ==> a[index] >= x
{}