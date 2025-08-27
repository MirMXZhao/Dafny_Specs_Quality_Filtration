function power(x: real, n: nat) : real
{}

method powerIter(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
{}

lemma {:induction e1} powDist(b: real, e1: nat, e2: nat)
    ensures power(b, e1+e2) == power(b, e1) * power(b, e2)
{}

lemma {:induction false} distributiveProperty(x: real, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, a+b)
{}

method powerOpt(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
{}

////////TESTS////////

method TestPowerIter1() {
  var p := powerIter(2.0, 3);
  assert p == power(2.0, 3);
}

method TestPowerIter2() {
  var p := powerIter(5.0, 0);
  assert p == power(5.0, 0);
}

method TestPowerOpt1() {
  var p := powerOpt(3.0, 2);
  assert p == power(3.0, 2);
}

method TestPowerOpt2() {
  var p := powerOpt(1.0, 10);
  assert p == power(1.0, 10);
}
