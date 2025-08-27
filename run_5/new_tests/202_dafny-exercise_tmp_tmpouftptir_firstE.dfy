method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1

{}

////////TESTS////////

method TestfirstE1() {
  var a := new char[5];
  a[0] := 'h';
  a[1] := 'e';
  a[2] := 'l';
  a[3] := 'l';
  a[4] := 'o';
  var x := firstE(a);
  assert x == 1;
}

method TestfirstE2() {
  var a := new char[3];
  a[0] := 'a';
  a[1] := 'b';
  a[2] := 'c';
  var x := firstE(a);
  assert x == -1;
}
