predicate sorted (a: array<int>)

	reads a
{}

predicate sortedA (a: array<int>, i: int)

	requires 0 <= i <= a.Length
	reads a
{}

method lookForMin (a: array<int>, i: int) returns (m: int)

	requires 0 <= i < a.Length
	ensures i <= m < a.Length
	ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
{}

method insertionSort (a: array<int>)

	modifies a
	ensures sorted(a)
{}
