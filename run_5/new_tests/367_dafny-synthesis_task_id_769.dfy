method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
{}

////////TESTS////////

method TestDifference1() {
  var a := [1, 2, 3, 4];
  var b := [2, 4, 6];
  var diff := Difference(a, b);
  assert diff == [1, 3];
}

method TestDifference2() {
  var a := [5, 7, 9];
  var b := [1, 2, 3];
  var diff := Difference(a, b);
  assert diff == [5, 7, 9];
}
