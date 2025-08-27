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

method TestPowerIter1() {
  var p := powerIter(2.0, 3);
  assert p == 8.0;
}

method TestPowerIter2() {
  var p := powerIter(5.0, 0);
  assert p == 1.0;
}

method TestPowerOpt1() {
  var p := powerOpt(3.0, 2);
  assert p == 9.0;
}

method TestPowerOpt2() {
  var p := powerOpt(10.0, 1);
  assert p == 10.0;
}
