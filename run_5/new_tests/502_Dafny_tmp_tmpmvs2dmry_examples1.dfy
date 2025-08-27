method Abs(x:int) returns (y:int)
ensures y>=0;
ensures x>=0 ==> x == y;
ensures x<0 ==> -x == y;
ensures y == abs(x);
{}

function abs(x: int): int{}

method MultiReturn(x:int, y:int) returns (more:int, less:int)
requires y>=0;
ensures less <= x <= more;
{}

method Max(x:int, y:int) returns (a:int)
ensures a == x || a == y;
ensures x > y ==> a == x;
ensures x <= y ==> a == y;
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

method TestMultiReturn1() {
  var more, less := MultiReturn(10, 5);
  assert less <= 10 <= more;
}

method TestMultiReturn2() {
  var more, less := MultiReturn(-2, 3);
  assert less <= -2 <= more;
}

method TestMax1() {
  var a := Max(8, 3);
  assert a == 8;
}

method TestMax2() {
  var a := Max(2, 7);
  assert a == 7;
}
