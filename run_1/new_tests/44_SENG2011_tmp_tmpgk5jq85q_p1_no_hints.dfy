method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall x :: 0 <= x < a.Length ==> b[x] == a[a.Length - x - 1]
{}

////////TESTS////////

method TestReverse1() {
  var a := new char[3] ['a', 'b', 'c'];
  var b := Reverse(a);
  assert b[0] == 'c' && b[1] == 'b' && b[2] == 'a';
}

method TestReverse2() {
  var a := new char[4] ['x', 'y', 'z', 'w'];
  var b := Reverse(a);
  assert b[0] == 'w' && b[1] == 'z' && b[2] == 'y' && b[3] == 'x';
}
