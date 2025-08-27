method {:verify true} FindRange(q: seq<int>, key: int) returns (left: nat, right: nat)
	requires Sorted(q)
	ensures left <= right <= |q|
	ensures forall i :: 0 <= i < left ==> q[i] < key
	ensures forall i :: left <= i < right ==> q[i] == key
	ensures forall i :: right <= i < |q| ==> q[i] > key
{}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate RangeSatisfiesComparer(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
	requires 0 <= lowerBound <= upperBound <= |q|
{
	forall i :: lowerBound <= i < upperBound ==> comparer(q[i], key)
}

predicate RangeSatisfiesComparerNegation(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
	requires 0 <= lowerBound <= upperBound <= |q|
{
	RangeSatisfiesComparer(q, key, lowerBound, upperBound, (n1, n2) => !comparer(n1, n2))
}

method BinarySearch(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool) returns (index: nat)
	requires Sorted(q)
	requires 0 <= lowerBound <= upperBound <= |q|
	requires RangeSatisfiesComparerNegation(q, key, 0, lowerBound, comparer)
	requires RangeSatisfiesComparer(q, key, upperBound, |q|, comparer)
	requires
		(forall n1, n2 :: comparer(n1, n2) == (n1 >  n2)) ||
		(forall n1, n2 :: comparer(n1, n2) == (n1 >= n2))

	ensures lowerBound <= index <= upperBound
	ensures RangeSatisfiesComparerNegation(q, key, 0, index, comparer)
	ensures RangeSatisfiesComparer(q, key, index, |q|, comparer)
{}

////////TESTS////////

method TestFindRange1() {
  var q := [1, 2, 2, 2, 5, 7];
  var left, right := FindRange(q, 2);
  assert left == 1;
  assert right == 4;
}

method TestFindRange2() {
  var q := [1, 3, 5, 7, 9];
  var left, right := FindRange(q, 4);
  assert left == 2;
  assert right == 2;
}
