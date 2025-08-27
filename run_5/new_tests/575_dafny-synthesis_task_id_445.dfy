method MultiplyElements(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] * b[i]
{}

////////TESTS////////

method TestMultiplyElements1() {
  var a := [1, 2, 3];
  var b := [4, 5, 6];
  var result := MultiplyElements(a, b);
  assert result == [4, 10, 18];
}

method TestMultiplyElements2() {
  var a := [2, -3, 0, 5];
  var b := [1, 2, 7, -1];
  var result := MultiplyElements(a, b);
  assert result == [2, -6, 0, -5];
}
