method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{}

////////TESTS////////

method TestRemoveChars1() {
  var v := RemoveChars("abcdef", "aeiou");
  assert v == "bcdf";
}

method TestRemoveChars2() {
  var v := RemoveChars("hello", "lo");
  assert v == "he";
}

method TestRemoveChars3() {
  var v := RemoveChars("", "abc");
  assert v == "";
}

method TestRemoveChars4() {
  var v := RemoveChars("xyz", "");
  assert v == "xyz";
}
