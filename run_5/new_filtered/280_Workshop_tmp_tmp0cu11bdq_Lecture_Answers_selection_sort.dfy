predicate sorted (a: array<int>)
	requires a != null
	reads a
{}

predicate sorted' (a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{}

method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted(a)
{}