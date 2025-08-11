predicate sorted(a: array?<int>, l: int, u: int)
	reads a
	requires a != null
	{}

method BinarySearch(a: array?<int>, key: int)
	returns (index: int)
	requires a != null && sorted(a,0,a.Length-1);
	ensures index >= 0 ==> index < a.Length && a[index] == key;
	ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
{}