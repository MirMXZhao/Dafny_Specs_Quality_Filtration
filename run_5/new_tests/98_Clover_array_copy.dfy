method iter_copy<T(0)>(s: array<T>) returns (t: array<T>)
  ensures s.Length==t.Length
  ensures forall i::0<=i<s.Length ==> s[i]==t[i]
{}

////////TESTS////////

method TestIterCopy1() {
  var s := new int[3];
  s[0] := 1;
  s[1] := 2;
  s[2] := 3;
  var t := iter_copy(s);
  assert t.Length == 3;
  assert t[0] == 1;
  assert t[1] == 2;
  assert t[2] == 3;
}

method TestIterCopy2() {
  var s := new string[0];
  var t := iter_copy(s);
  assert t.Length == 0;
}
