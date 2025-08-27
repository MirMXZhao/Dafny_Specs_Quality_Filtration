method AddLists(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
{}

////////TESTS////////

method TestAddLists1() {
  var a := [1, 2, 3];
  var b := [4, 5, 6];
  var result := AddLists(a, b);
  assert result == [5, 7, 9];
}

method TestAddLists2() {
  var a := [10, -3, 0];
  var b := [-5, 8, 2];
  var result := AddLists(a, b);
  assert result == [5, 5, 2];
}
