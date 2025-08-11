method ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int) returns (element: int)
    requires n >= 0
    requires 0 <= index < |l|
    ensures element == l[(index - n + |l|) % |l|]
{}

////////TESTS////////

method TestElementAtIndexAfterRotation1() {
  var l := [1, 2, 3, 4, 5];
  var element := ElementAtIndexAfterRotation(l, 2, 3);
  assert element == 2;
}

method TestElementAtIndexAfterRotation2() {
  var l := [10, 20, 30];
  var element := ElementAtIndexAfterRotation(l, 1, 0);
  assert element == 30;
}
