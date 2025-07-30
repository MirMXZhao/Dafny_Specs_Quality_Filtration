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

method testpower1() {
  var result := power(2.0, 3);
  assert result == 8.0;
}

method testpower2() {
  var result := power(5.0, 0);
  assert result == 1.0;
}

method testpower3() {
  var result := power(3.0, 1);
  assert result == 3.0;
}

method testpowerIter1() {
  var p := powerIter(2.0, 3);
  assert p == 8.0;
}

method testpowerIter2() {
  var p := powerIter(3.0, 2);
  assert p == 9.0;
}

method testpowerIter3() {
  var p := powerIter(7.0, 0);
  assert p == 1.0;
}

method testpowerOpt1() {
  var p := powerOpt(2.0, 4);
  assert p == 16.0;
}

method testpowerOpt2() {
  var p := powerOpt(1.0, 5);
  assert p == 1.0;
}

method testpowerOpt3() {
  var p := powerOpt(4.0, 2);
  assert p == 16.0;
}

method testdistributiveProperty1() {
  distributiveProperty(2.0, 2, 3);
  assert power(2.0, 2) * power(2.0, 3) == power(2.0, 5);
}

method testdistributiveProperty2() {
  distributiveProperty(3.0, 1, 0);
  assert power(3.0, 1) * power(3.0, 0) == power(3.0, 1);
}
