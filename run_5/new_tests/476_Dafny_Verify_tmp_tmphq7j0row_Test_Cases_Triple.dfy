method Triple(x: int) returns (r: int)
{}

method TripleIf(x: int) returns (r: int) {}

method TripleOver(x: int) returns (r: int) {}

method TripleConditions(x: int) returns (r: int) 
requires x % 2 == 0
ensures r == 3 * x
{}

////////TESTS////////

method TestTriple1() {
  var r := Triple(5);
  assert r == 15;
}

method TestTriple2() {
  var r := Triple(-3);
  assert r == -9;
}

method TestTripleIf1() {
  var r := TripleIf(4);
  assert r == 12;
}

method TestTripleIf2() {
  var r := TripleIf(0);
  assert r == 0;
}

method TestTripleOver1() {
  var r := TripleOver(7);
  assert r == 21;
}

method TestTripleOver2() {
  var r := TripleOver(-2);
  assert r == -6;
}

method TestTripleConditions1() {
  var r := TripleConditions(6);
  assert r == 18;
}

method TestTripleConditions2() {
  var r := TripleConditions(-4);
  assert r == -12;
}
