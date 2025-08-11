method SubtractSequences(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] - b[i]
{}

////////TESTS////////

method TestSubtractSequences1() {
  var a := [5, 8, 3, 7];
  var b := [2, 3, 1, 4];
  var result := SubtractSequences(a, b);
  assert result == [3, 5, 2, 3];
}

method TestSubtractSequences2() {
  var a := [10, -5, 0];
  var b := [3, -2, 7];
  var result := SubtractSequences(a, b);
  assert result == [7, -3, -7];
}
