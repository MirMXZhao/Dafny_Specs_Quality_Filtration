function Power(n: nat): nat {}

method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{}

////////TESTS////////

method TestComputePower1() {
  var y := ComputePower(3);
  assert y == Power(3);
}

method TestComputePower2() {
  var y := ComputePower(0);
  assert y == Power(0);
}
