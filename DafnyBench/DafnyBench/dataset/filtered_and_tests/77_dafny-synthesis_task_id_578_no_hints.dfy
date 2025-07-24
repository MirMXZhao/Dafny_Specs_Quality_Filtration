method Interleave(s1: seq<int>, s2: seq<int>, s3: seq<int>) returns (r: seq<int>)
    requires |s1| == |s2| && |s2| == |s3|
    ensures |r| == 3 * |s1|
    ensures forall i :: 0 <= i < |s1| ==> r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i]
{}

method TestInterleave1() {
  var s1 := [1, 4, 7];
  var s2 := [2, 5, 8];
  var s3 := [3, 6, 9];
  var r := Interleave(s1, s2, s3);
  assert r == [1, 2, 3, 4, 5, 6, 7, 8, 9];
}

method TestInterleave2() {
  var s1 := [10, 30];
  var s2 := [20, 40];
  var s3 := [25, 35];
  var r := Interleave(s1, s2, s3);
  assert r == [10, 20, 25, 30, 40, 35];
}
