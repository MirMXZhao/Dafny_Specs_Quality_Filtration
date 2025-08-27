method fillK(a: array<int>, n: int, k: int, c: int) returns (b: bool)
    requires 0 <= c <= n
    requires n == a.Length
{}


method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
    requires 0 <= b.Length <= a.Length
{}

////////TESTS////////

method TestFillK1() {
  var a := new int[5];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4; a[4] := 5;
  var b := fillK(a, 5, 10, 3);
  assert b == true;
}

method TestFillK2() {
  var a := new int[3];
  a[0] := 7; a[1] := 8; a[2] := 9;
  var b := fillK(a, 3, 5, 0);
  assert b == false;
}

method TestContainsSubString1() {
  var a := new char[7];
  a[0] := 'h'; a[1] := 'e'; a[2] := 'l'; a[3] := 'l'; a[4] := 'o'; a[5] := 'w'; a[6] := 'd';
  var b := new char[3];
  b[0] := 'l'; b[1] := 'l'; b[2] := 'o';
  var pos := containsSubString(a, b);
  assert pos == 2;
}

method TestContainsSubString2() {
  var a := new char[5];
  a[0] := 'a'; a[1] := 'b'; a[2] := 'c'; a[3] := 'd'; a[4] := 'e';
  var b := new char[2];
  b[0] := 'x'; b[1] := 'y';
  var pos := containsSubString(a, b);
  assert pos == -1;
}
