method firste(a: array<char>) returns (c:int)
ensures -1 <= c < a.Length
ensures 0 <= c < a.Length ==> a[c] == 'e' && forall x :: 0 <= x < c ==> a[x] != 'e'
ensures c == -1 ==> forall x :: 0 <= x < a.Length ==> a[x] != 'e'
{}

////////TESTS////////

method Testfirste1() {
  var a := new char[5] ['h', 'e', 'l', 'l', 'o'];
  var c := firste(a);
  assert c == 1;
}

method Testfirste2() {
  var a := new char[3] ['c', 'a', 't'];
  var c := firste(a);
  assert c == -1;
}
