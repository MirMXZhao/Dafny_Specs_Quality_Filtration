method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
{}

method TestExtractRearChars1() {
  var l := ["hello", "world", "test"];
  var r := ExtractRearChars(l);
  assert r == ['o', 'd', 't'];
}

method TestExtractRearChars2() {
  var l := ["a", "bb", "ccc"];
  var r := ExtractRearChars(l);
  assert r == ['a', 'b', 'c'];
}
