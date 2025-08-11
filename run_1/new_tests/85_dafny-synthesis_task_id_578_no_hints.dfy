method Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>) returns (r: seq<int>)
    requires |s1| == |s2| && |s2| == |s3|
    ensures |r| == 3 * |s1|
    ensures forall i :: 0 <= i < |s1| ==> r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i]
{}

////////TESTS////////

method TestInterleave1() {
  var s1 := [1, 3, 5];
  var s2 := [2, 4, 6];
  var s3 := [7, 8, 9];
  var r := Interleave(s1, s2, s3);
  assert r == [1, 2, 7, 3, 4, 8, 5, 6, 9];
}

method TestInterleave2() {
  var s1 := [10, 20];
  var s2 := [30, 40];
  var s3 := [50, 60];
  var r := Interleave(s1, s2, s3);
  assert r == [10, 30, 50, 20, 40, 60];
}
