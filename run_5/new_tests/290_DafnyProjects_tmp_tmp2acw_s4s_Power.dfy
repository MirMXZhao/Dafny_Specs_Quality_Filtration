function power(x: real, n: nat) : real {}

method powerDC(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{}

lemma {:induction a} productOfPowers(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{ }

////////TESTS////////

method TestPowerDC1() {
  var p := powerDC(2.0, 3);
  assert p == 8.0;
}

method TestPowerDC2() {
  var p := powerDC(5.0, 0);
  assert p == 1.0;
}
