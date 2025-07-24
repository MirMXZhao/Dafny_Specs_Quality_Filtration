method ElementWiseDivide(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |b| ==> b[i] != 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] / b[i]
{}


method TestElementWiseDivide1() {
  var a := [10, 15, 8];
  var b := [2, 3, 4];
  var result := ElementWiseDivide(a, b);
  assert result == [5, 5, 2];
}

method TestElementWiseDivide2() {
  var a := [9, -12, 7];
  var b := [3, -4, 1];
  var result := ElementWiseDivide(a, b);
  assert result == [3, 3, 7];
}
