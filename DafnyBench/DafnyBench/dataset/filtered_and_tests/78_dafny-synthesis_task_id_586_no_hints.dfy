method SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0 && n < |l|
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
{}

method TestSplitAndAppend1() {
  var l := [1, 2, 3, 4, 5];
  var r := SplitAndAppend(l, 2);
  assert r == [3, 4, 5, 1, 2];
}

method TestSplitAndAppend2() {
  var l := [10, 20, 30];
  var r := SplitAndAppend(l, 1);
  assert r == [20, 30, 10];
}
