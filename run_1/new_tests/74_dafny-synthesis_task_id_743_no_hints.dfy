method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{}

////////TESTS////////

method TestRotateRight1() {
  var l := [1, 2, 3, 4, 5];
  var n := 2;
  var r := RotateRight(l, n);
  assert r == [4, 5, 1, 2, 3];
}

method TestRotateRight2() {
  var l := [10, 20, 30];
  var n := 0;
  var r := RotateRight(l, n);
  assert r == [10, 20, 30];
}
