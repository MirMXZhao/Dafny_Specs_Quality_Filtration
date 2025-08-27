function power(a: int, n: int): int
  requires 0 <= a && 0 <= n;
  decreases n;{}

method compute_power(a: int, n: int) returns (s: int)
  requires n >= 0 && a >= 0;
  ensures s == power(a,n);
{}

////////TESTS////////

method TestComputePower1() {
  var s := compute_power(2, 3);
  assert s == 8;
}

method TestComputePower2() {
  var s := compute_power(5, 0);
  assert s == 1;
}
