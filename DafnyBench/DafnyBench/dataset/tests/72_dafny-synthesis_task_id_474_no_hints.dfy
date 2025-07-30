method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
{}

////////TESTS////////

method TestReplaceChars1() {
  var v := ReplaceChars("hello", 'l', 'x');
  assert v == "hexxo";
}

method TestReplaceChars2() {
  var v := ReplaceChars("world", 'z', 'y');
  assert v == "world";
}

method TestReplaceChars3() {
  var v := ReplaceChars("", 'a', 'b');
  assert v == "";
}
