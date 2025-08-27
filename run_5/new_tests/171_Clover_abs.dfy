method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{}

////////TESTS////////

method TestAbs1() {
  var y := Abs(5);
  assert y == 5;
}

method TestAbs2() {
  var y := Abs(-3);
  assert y == 3;
}
