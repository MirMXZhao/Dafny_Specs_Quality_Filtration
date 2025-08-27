method Fact(x: int) returns (y: int)
  requires x >= 0;   
{}

////////TESTS////////

method TestFact1() {
  var y := Fact(5);
  assert y == 120;
}

method TestFact2() {
  var y := Fact(0);
  assert y == 1;
}
