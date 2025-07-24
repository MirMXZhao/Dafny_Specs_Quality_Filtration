method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
{}

method TestReplaceChars1() {
  var result := ReplaceChars("hello world", 'l', 'x');
  assert result == "hexxo worxd";
}

method TestReplaceChars2() {
  var result := ReplaceChars("abcdef", 'z', 'y');
  assert result == "abcdef";
}
