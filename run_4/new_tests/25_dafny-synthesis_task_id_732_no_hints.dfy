predicate IsSpaceCommaDot(c: char)
{}

method ReplaceWithColon(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{}

////////TESTS////////

method TestReplaceWithColon1() {
  var s := "hello, world.";
  var v := ReplaceWithColon(s);
  assert v == "hello: world:";
}

method TestReplaceWithColon2() {
  var s := "abc def";
  var v := ReplaceWithColon(s);
  assert v == "abc:def";
}
