method AppendArrayToSeq(s: seq<int>, a: array<int>) returns (r: seq<int>)
    requires a != null
    ensures |r| == |s| + a.Length
    ensures forall i :: 0 <= i < |s| ==> r[i] == s[i]
    ensures forall i :: 0 <= i < a.Length ==> r[|s| + i] == a[i]
{}

////////TESTS////////

method TestAppendArrayToSeq1() {
  var s := [1, 2, 3];
  var a := new int[2];
  a[0] := 4;
  a[1] := 5;
  var r := AppendArrayToSeq(s, a);
  assert r == [1, 2, 3, 4, 5];
}

method TestAppendArrayToSeq2() {
  var s := [];
  var a := new int[3];
  a[0] := 7;
  a[1] := 8;
  a[2] := 9;
  var r := AppendArrayToSeq(s, a);
  assert r == [7, 8, 9];
}
