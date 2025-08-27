method SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
{}

////////TESTS////////

method TestSplitStringIntoChars1() {
  var s := "hello";
  var v := SplitStringIntoChars(s);
  assert v == ['h', 'e', 'l', 'l', 'o'];
}

method TestSplitStringIntoChars2() {
  var s := "";
  var v := SplitStringIntoChars(s);
  assert v == [];
}
