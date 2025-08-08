method MultiplyElements(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] * b[i]
{}

////////TESTS////////

method TestMultiplyElements1() {
  var a := [2, 3, 4];
  var b := [5, 6, 7];
  var result := MultiplyElements(a, b);
  assert result == [10, 18, 28];
}

method TestMultiplyElements2() {
  var a := [1, -2, 0];
  var b := [3, 4, 5];
  var result := MultiplyElements(a, b);
  assert result == [3, -8, 0];
}
