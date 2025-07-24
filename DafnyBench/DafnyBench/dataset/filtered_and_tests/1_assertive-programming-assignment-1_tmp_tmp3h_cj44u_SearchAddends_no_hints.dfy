method Main()
{}

predicate Sorted(q: seq<int>)
{}

predicate HasAddends(q: seq<int>, x: int)
{}

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
	requires Sorted(q) && HasAddends(q, x)
	ensures i < j < |q| && q[i]+q[j] == x
{}

predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
	0 <= i < |q|
}

predicate AreOreredIndices<T>(q: seq<T>, i: nat, j: nat)
{
	0 <= i < j < |q|
}

predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
	requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
	q[i] + q[j] == x
}

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
	requires AreOreredIndices(q, i, j)
{}

predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{}

lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
	requires HasAddends(q, x)
	requires Sorted(q)
	requires sum > x;
	requires LoopInv(q, x, i, j, sum)
	ensures HasAddendsInIndicesRange(q, x, i, j - 1)
{
}



method TestFindAddends1() {
  var q := [1, 2, 3, 4, 5];
  assume Sorted(q) && HasAddends(q, 7);
  var i, j := FindAddends(q, 7);
  assert i < j < |q| && q[i] + q[j] == 7;
}

method TestFindAddends2() {
  var q := [2, 5, 8, 12, 15];
  assume Sorted(q) && HasAddends(q, 20);
  var i, j := FindAddends(q, 20);
  assert i < j < |q| && q[i] + q[j] == 20;
}
