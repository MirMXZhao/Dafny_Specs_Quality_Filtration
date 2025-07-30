method SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0 && n < |l|
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
{}

////////TESTS////////

method TestSplitAndAppend1() {
  var l := [1, 2, 3, 4, 5];
  var n := 2;
  var r := SplitAndAppend(l, n);
  assert r == [3, 4, 5, 1, 2];
}

method TestSplitAndAppend2() {
  var l := [10, 20, 30];
  var n := 1;
  var r := SplitAndAppend(l, n);
  assert r == [20, 30, 10];
}

method TestSplitAndAppend3() {
  var l := [7, 8];
  var n := 0;
  var r := SplitAndAppend(l, n);
  assert r == [7, 8];
}
