function fact(n: nat): nat 
    ensures fact(n) >= 1
{}

method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
{}

////////TESTS////////

method Testfact1() {
  var result := fact(0);
  assert result == 1;
}

method Testfact2() {
  var result := fact(5);
  assert result == 120;
}

method Testfactorial1() {
  var res := factorial(0);
  assert res == 1;
}

method Testfactorial2() {
  var res := factorial(4);
  assert res == 24;
}
