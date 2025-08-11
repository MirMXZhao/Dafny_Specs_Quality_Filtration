method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{}

////////TESTS////////

method TestReplaceBlanksWithChar1() {
  var result := ReplaceBlanksWithChar("hello world", '_');
  assert result == "hello_world";
}

method TestReplaceBlanksWithChar2() {
  var result := ReplaceBlanksWithChar("no spaces", 'X');
  assert result == "no spaces";
}
