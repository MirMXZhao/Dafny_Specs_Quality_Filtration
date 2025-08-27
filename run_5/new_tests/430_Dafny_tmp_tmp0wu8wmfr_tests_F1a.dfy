method F() returns ( r: int)
    ensures r <= 0
{
    r := 0;
}


method Mid( p: int, q: int) returns ( m: int )
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;

{}

////////TESTS////////

method TestF1() {
  var r := F();
  assert r <= 0;
}

method TestF2() {
  var r := F();
  assert r <= 0;
}

method TestMid1() {
  var m := Mid(5, 10);
  assert 5 <= m <= 10;
  assert m - 5 <= 10 - m;
  assert 0 <= (10 - m) - (m - 5) <= 1;
}

method TestMid2() {
  var m := Mid(0, 4);
  assert 0 <= m <= 4;
  assert m - 0 <= 4 - m;
  assert 0 <= (4 - m) - (m - 0) <= 1;
}
