method GetFirstElements(lst: seq<seq<int>>) returns (result: seq<int>)
    requires forall i :: 0 <= i < |lst| ==> |lst[i]| > 0
    ensures |result| == |lst|
    ensures forall i :: 0 <= i < |result| ==> result[i] == lst[i][0]
{}

////////TESTS////////

method TestGetFirstElements1() {
  var lst := [[1, 2, 3], [4, 5], [6, 7, 8, 9]];
  var result := GetFirstElements(lst);
  assert result == [1, 4, 6];
}

method TestGetFirstElements2() {
  var lst := [[10], [20, 30], [40, 50, 60]];
  var result := GetFirstElements(lst);
  assert result == [10, 20, 40];
}

method TestGetFirstElements3() {
  var lst: seq<seq<int>> := [];
  var result := GetFirstElements(lst);
  assert result == [];
}
