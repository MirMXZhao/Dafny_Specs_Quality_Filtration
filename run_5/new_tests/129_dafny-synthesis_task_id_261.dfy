method ElementWiseDivision(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
{}

////////TESTS////////

method TestElementWiseDivision1() {
  var a := [10, 15, 8];
  var b := [2, 3, 4];
  var result := ElementWiseDivision(a, b);
  assert result == [5, 5, 2];
}

method TestElementWiseDivision2() {
  var a := [7, -12, 9, 0];
  var b := [1, -4, 3, 5];
  var result := ElementWiseDivision(a, b);
  assert result == [7, 3, 3, 0];
}
