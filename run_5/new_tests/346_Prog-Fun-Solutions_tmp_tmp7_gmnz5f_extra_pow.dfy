ghost function pow(a: int, e: nat): int {}

method Pow(a: nat, n: nat) returns (y: nat)
ensures y == pow(a, n)
{}

////////TESTS////////

method TestPow1() {
  var y := Pow(2, 3);
  assert y == 8;
}

method TestPow2() {
  var y := Pow(5, 0);
  assert y == 1;
}
