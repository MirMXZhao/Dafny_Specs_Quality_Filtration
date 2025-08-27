method Min(x: int, y:int) returns (z: int)
  ensures x<=y ==> z==x
  ensures x>y ==> z==y
{}

////////TESTS////////

method TestMin1() {
  var z := Min(3, 7);
  assert z == 3;
}

method TestMin2() {
  var z := Min(9, 4);
  assert z == 4;
}
