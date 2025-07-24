//https://homepage.cs.uiowa.edu/~tinelli/classes/181/Fall21/Tools/Dafny/Examples/selection-sort.shtml

predicate sorted (a: array<int>)
	requires a != null
	reads a
{}

predicate sorted' (a: array<int>, i: int)
	requires a != null
	requires 0 <= i <= a.Length
	reads a
{}


// Selection sort on arrays

method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted(a)
  //ensures multiset(old(a[..])) == multiset(a[..])
{}
