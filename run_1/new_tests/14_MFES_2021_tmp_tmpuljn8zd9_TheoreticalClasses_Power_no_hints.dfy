function power(x: real, n: nat) : real
{}

method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{}

method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
{}

lemma {:induction a} distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{}

////////TESTS////////

method TestPower1() {
  var p := power(2.0, 3);
  assert p == 8.0;
}

method TestPower2() {
  var p := power(5.0, 0);
  assert p == 1.0;
}

method TestPowerIter1() {
  var p := powerIter(3.0, 2);
  assert p == 9.0;
}

method TestPowerIter2() {
  var p := powerIter(4.0, 1);
  assert p == 4.0;
}

method TestPowerOpt1() {
  var p := powerOpt(2.5, 2);
  assert p == 6.25;
}

method TestPowerOpt2() {
  var p := powerOpt(7.0, 0);
  assert p == 1.0;
}
