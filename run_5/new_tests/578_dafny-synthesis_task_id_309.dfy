method Max(a: int, b: int) returns (maxValue: int)
    ensures maxValue == a || maxValue == b
    ensures maxValue >= a && maxValue >= b
{}

////////TESTS////////

method TestMax1() {
  var maxValue := Max(5, 3);
  assert maxValue == 5;
}

method TestMax2() {
  var maxValue := Max(2, 8);
  assert maxValue == 8;
}
