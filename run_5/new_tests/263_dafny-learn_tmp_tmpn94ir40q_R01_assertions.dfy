method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
{}

method Max(a: int, b: int) returns (c: int)
  ensures c >= a
  ensures c >= b
{}

////////TESTS////////

method TestAbs1() {
  var y := Abs(-5);
  assert y == 5;
}

method TestAbs2() {
  var y := Abs(3);
  assert y == 3;
}

method TestMax1() {
  var c := Max(7, 3);
  assert c == 7;
}

method TestMax2() {
  var c := Max(-2, 5);
  assert c == 5;
}
