method ArrayToSeq(a: array<int>) returns (s: seq<int>)
    requires a != null
    ensures |s| == a.Length
    ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
{}

////////TESTS////////

method TestArrayToSeq1() {
  var a := new int[3];
  a[0] := 10;
  a[1] := 20;
  a[2] := 30;
  var s := ArrayToSeq(a);
  assert s == [10, 20, 30];
}

method TestArrayToSeq2() {
  var a := new int[0];
  var s := ArrayToSeq(a);
  assert s == [];
}
