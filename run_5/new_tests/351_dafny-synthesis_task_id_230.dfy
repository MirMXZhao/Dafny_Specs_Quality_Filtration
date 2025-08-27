method ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{}

////////TESTS////////

method TestReplaceBlanksWithChar1() {
  var s := "hello world";
  var ch := '_';
  var v := ReplaceBlanksWithChar(s, ch);
  assert v == "hello_world";
}

method TestReplaceBlanksWithChar2() {
  var s := "no spaces";
  var ch := '*';
  var v := ReplaceBlanksWithChar(s, ch);
  assert v == "no*spaces";
}
