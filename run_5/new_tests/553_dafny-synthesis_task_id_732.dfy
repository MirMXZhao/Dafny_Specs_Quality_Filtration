predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}

method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{}

////////TESTS////////

method TestReplaceWithColon1() {
  var s := "hello, world. test";
  var v := ReplaceWithColon(s);
  assert v == "hello: world: test";
}

method TestReplaceWithColon2() {
  var s := "no spaces";
  var v := ReplaceWithColon(s);
  assert v == "no:spaces";
}
