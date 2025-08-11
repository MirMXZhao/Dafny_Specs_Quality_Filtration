method ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
{}

////////TESTS////////

method TestElementWiseDivide1() {
  var a := [10, 20, 30];
  var b := [2, 4, 5];
  var result := ElementWiseDivide(a, b);
  assert result == [5, 5, 6];
}

method TestElementWiseDivide2() {
  var a := [7, 15, 8];
  var b := [1, 3, 2];
  var result := ElementWiseDivide(a, b);
  assert result == [7, 5, 4];
}
