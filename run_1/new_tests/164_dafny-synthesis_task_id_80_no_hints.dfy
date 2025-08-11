method TetrahedralNumber(n: int) returns (t: int)
    requires n >= 0
    ensures t == n * (n + 1) * (n + 2) / 6
{}

////////TESTS////////

method TestTetrahedralNumber1() {
  var t := TetrahedralNumber(3);
  assert t == 10;
}

method TestTetrahedralNumber2() {
  var t := TetrahedralNumber(0);
  assert t == 0;
}
