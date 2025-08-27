method Main(xInit: int, y: int) returns (z: int)
  requires xInit >= 0
  requires y >= 0
  ensures z == 0
{}

////////TESTS////////

method TestMain1() {
  var z := Main(5, 3);
  assert z == 0;
}

method TestMain2() {
  var z := Main(0, 10);
  assert z == 0;
}
