function power(a: int, n: int): int
  requires 0 <= n;
  decreases n;{}


method A8Q1(y0: int, x: int) returns (z: int)
requires y0 >= 0;
ensures z==power(x,y0);
{}

////////TESTS////////

method TestA8Q11() {
  var z := A8Q1(3, 2);
  assert z == 8;
}

method TestA8Q12() {
  var z := A8Q1(0, 5);
  assert z == 1;
}
