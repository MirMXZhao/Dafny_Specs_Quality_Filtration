method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{}

////////TESTS////////

method TestRemoveChars1() {
  var v := RemoveChars("abcdef", "ace");
  assert v == "bdf";
}

method TestRemoveChars2() {
  var v := RemoveChars("hello", "xyz");
  assert v == "hello";
}
