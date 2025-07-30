method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{}

////////TESTS////////

method TestRotateRight1() {
  var l := [1, 2, 3, 4, 5];
  var r := RotateRight(l, 2);
  assert r == [4, 5, 1, 2, 3];
}

method TestRotateRight2() {
  var l := [1, 2, 3];
  var r := RotateRight(l, 0);
  assert r == [1, 2, 3];
}

method TestRotateRight3() {
  var l := [10, 20];
  var r := RotateRight(l, 3);
  assert r == [20, 10];
}

method TestRotateRight4() {
  var l: seq<int> := [];
  var r := RotateRight(l, 5);
  assert r == [];
}
