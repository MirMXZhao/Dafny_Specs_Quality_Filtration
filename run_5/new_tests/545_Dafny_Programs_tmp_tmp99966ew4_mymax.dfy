method Max(a: int, b:int) returns (c: int)
    ensures c >= a && c>= b
{}

////////TESTS////////

method TestMax1() {
  var c := Max(5, 3);
  assert c == 5;
}

method TestMax2() {
  var c := Max(-2, 7);
  assert c == 7;
}
