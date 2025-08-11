method IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |a| > 0 && |b| > 0
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
{}

////////TESTS////////

method TestIndexWiseAddition1() {
  var a := [[1, 2], [3, 4]];
  var b := [[5, 6], [7, 8]];
  var result := IndexWiseAddition(a, b);
  assert result == [[6, 8], [10, 12]];
}

method TestIndexWiseAddition2() {
  var a := [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
  var b := [[9, 8, 7], [6, 5, 4], [3, 2, 1]];
  var result := IndexWiseAddition(a, b);
  assert result == [[10, 10, 10], [10, 10, 10], [10, 10, 10]];
}
