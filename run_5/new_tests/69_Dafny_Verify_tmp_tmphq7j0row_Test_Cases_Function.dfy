function Average (a: int, b: int): int 
{
    (a + b) / 2
}

method TripleConditions(x: int) returns (r: int) 
ensures r == 3 * x
{}

method Triple' (x: int) returns (r: int) 
    ensures Average(r, 3 * x) == 3 * x
    ensures r == 3 * x
{
    r:= 3 * x;
}

////////TESTS////////

method TestTripleConditions1() {
  var r := TripleConditions(5);
  assert r == 15;
}

method TestTripleConditions2() {
  var r := TripleConditions(-3);
  assert r == -9;
}

method TestTriple'1() {
  var r := Triple'(4);
  assert r == 12;
}

method TestTriple'2() {
  var r := Triple'(0);
  assert r == 0;
}
