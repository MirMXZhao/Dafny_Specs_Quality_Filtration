method sumOdds(n: nat) returns (sum: nat)
    requires n > 0;
    ensures sum == n * n;
{}

method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 

method intDivImpl(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 
{}

////////TESTS////////

method TestSumOdds1() {
  var sum := sumOdds(3);
  assert sum == 9;
}

method TestSumOdds2() {
  var sum := sumOdds(5);
  assert sum == 25;
}

method TestIntDiv1() {
  var q, r := intDiv(10, 3);
  assert q == 3;
  assert r == 1;
}

method TestIntDiv2() {
  var q, r := intDiv(15, 4);
  assert q == 3;
  assert r == 3;
}

method TestIntDivImpl1() {
  var q, r := intDivImpl(14, 5);
  assert q == 2;
  assert r == 4;
}

method TestIntDivImpl2() {
  var q, r := intDivImpl(8, 2);
  assert q == 4;
  assert r == 0;
}
