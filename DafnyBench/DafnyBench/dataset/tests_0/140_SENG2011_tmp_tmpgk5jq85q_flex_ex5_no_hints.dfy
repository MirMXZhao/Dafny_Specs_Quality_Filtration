method firste(a: array<char>) returns (c:int)
ensures -1 <= c < a.Length
ensures 0 <= c < a.Length ==> a[c] == 'e' && forall x :: 0 <= x < c ==> a[x] != 'e'
ensures c == -1 ==> forall x :: 0 <= x < a.Length ==> a[x] != 'e'
{}

////////TESTS////////

method testfirste1() {
  var a := new char[5];
  a[0] := 'h';
  a[1] := 'e';
  a[2] := 'l';
  a[3] := 'l';
  a[4] := 'o';
  var c := firste(a);
  assert c == 1;
}

method testfirste2() {
  var a := new char[3];
  a[0] := 'a';
  a[1] := 'b';
  a[2] := 'c';
  var c := firste(a);
  assert c == -1;
}

method testfirste3() {
  var a := new char[0];
  var c := firste(a);
  assert c == -1;
}
