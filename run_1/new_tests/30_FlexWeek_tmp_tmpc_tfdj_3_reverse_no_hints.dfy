method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall k :: 0 <= k < a.Length ==> b[k] == a[(a.Length-1) - k];
{}

////////TESTS////////

method TestReverse1() {
  var a := new char[4];
  a[0] := 'a';
  a[1] := 'b';
  a[2] := 'c';
  a[3] := 'd';
  var b := Reverse(a);
  assert b[0] == 'd';
  assert b[1] == 'c';
  assert b[2] == 'b';
  assert b[3] == 'a';
}

method TestReverse2() {
  var a := new char[3];
  a[0] := 'x';
  a[1] := 'y';
  a[2] := 'z';
  var b := Reverse(a);
  assert b[0] == 'z';
  assert b[1] == 'y';
  assert b[2] == 'x';
}
