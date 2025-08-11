method SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
{}

////////TESTS////////

method TestSmallestListLength1() {
  var s := [[1, 2, 3], [4, 5], [6, 7, 8, 9]];
  var v := SmallestListLength(s);
  assert v == 2;
}

method TestSmallestListLength2() {
  var s := [[1], [2, 3, 4], [5, 6]];
  var v := SmallestListLength(s);
  assert v == 1;
}
