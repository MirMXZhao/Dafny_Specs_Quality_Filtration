predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
{}

////////TESTS////////

method TestInsertionSort1() {
  var s := [3, 1, 4, 1, 5];
  var r := InsertionSort(s);
  assert r == [1, 1, 3, 4, 5];
}

method TestInsertionSort2() {
  var s := [5, 2, 8, 1, 9];
  var r := InsertionSort(s);
  assert r == [1, 2, 5, 8, 9];
}
