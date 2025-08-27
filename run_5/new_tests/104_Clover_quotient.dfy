method Quotient(x: nat, y:nat) returns (r:int, q:int)
  requires y != 0
  ensures q * y + r == x && 0 <= r < y && 0 <= q
{}

////////TESTS////////

method TestQuotient1() {
  var r, q := Quotient(10, 3);
  assert r == 1;
  assert q == 3;
}

method TestQuotient2() {
  var r, q := Quotient(15, 5);
  assert r == 0;
  assert q == 3;
}
