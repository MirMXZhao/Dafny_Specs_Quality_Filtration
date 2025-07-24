method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
{}

method TestRemoveChars1() {
  var result := RemoveChars("abcdef", "aeiou");
  assert result == "bcdf";
}

method TestRemoveChars2() {
  var result := RemoveChars("hello", "lo");
  assert result == "he";
}
