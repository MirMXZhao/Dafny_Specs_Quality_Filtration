function Power(n: nat): nat {}

method ComputePower(n: nat) returns (p: nat)
    ensures p == Power(n)
{}

////////TESTS////////

method TestComputePower1() {
  var p := ComputePower(3);
  assert p == Power(3);
}

method TestComputePower2() {
  var p := ComputePower(0);
  assert p == Power(0);
}
