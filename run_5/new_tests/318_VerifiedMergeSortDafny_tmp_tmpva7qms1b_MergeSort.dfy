method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires 0 <= start <= end <= b.Length
  requires |a1| +  |a2| == end - start + 1
  ensures sorted_slice(b, start, end)
{}

method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires end - start == |a1| + |a2|
  requires 0 <= start < end < |a1| && end <= |a2| < b.Length
  requires end < |a1| && end < |a2|
  ensures sorted_slice(b, start, end)
  requires b.Length == |a2| + |a1|
  ensures merged(a1, a2, b, start, end)
{}

predicate merged(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, end: int)
  reads b
  requires end - start  == |a2| + |a1|
  requires 0 <= start <= end <= b.Length
{}

predicate sorted_slice(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  reads a
{}

predicate sorted_seq(a: seq<int>)
{
  forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

predicate sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

////////TESTS////////

method TestMergeSimple1() {
  var a1 := [1, 3, 5];
  var a2 := [2, 4, 6];
  var b := new int[6];
  mergeSimple(a1, a2, 0, 5, b);
}

method TestMergeSimple2() {
  var a1 := [1, 2];
  var a2 := [3, 4, 5];
  var b := new int[7];
  mergeSimple(a1, a2, 1, 5, b);
}

method TestMerge1() {
  var a1 := [1, 3];
  var a2 := [2, 4];
  var b := new int[4];
  merge(a1, a2, 0, 3, b);
}

method TestMerge2() {
  var a1 := [1];
  var a2 := [2, 3];
  var b := new int[3];
  merge(a1, a2, 0, 2, b);
}
