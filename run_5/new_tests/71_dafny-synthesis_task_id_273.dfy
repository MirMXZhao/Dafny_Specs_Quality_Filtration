method SubtractSequences(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] - b[i]
{}

////////TESTS////////

method TestSubtractSequences1() {
  var a := [5, 8, 3, 1];
  var b := [2, 4, 1, 0];
  var result := SubtractSequences(a, b);
  assert result == [3, 4, 2, 1];
}

method TestSubtractSequences2() {
  var a := [10, -3, 7];
  var b := [4, -1, 9];
  var result := SubtractSequences(a, b);
  assert result == [6, -2, -2];
}
