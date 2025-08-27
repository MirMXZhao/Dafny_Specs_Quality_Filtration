method simple(y: int) returns (x: int) 
  requires y==6;
  ensures x==7;
{}

////////TESTS////////

method TestSimple1() {
  var x := simple(6);
  assert x == 7;
}

method TestSimple2() {
  var x := simple(6);
  assert x == 7;
}
