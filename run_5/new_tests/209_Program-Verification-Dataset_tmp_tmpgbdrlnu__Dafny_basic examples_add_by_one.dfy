method add_by_one (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
{}

method bar (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
{}

////////TESTS////////

method Testadd_by_one1() {
  var r := add_by_one(5, 3);
  assert r == 8;
}

method Testadd_by_one2() {
  var r := add_by_one(-2, 7);
  assert r == 5;
}

method Testbar1() {
  var r := bar(10, 4);
  assert r == 14;
}

method Testbar2() {
  var r := bar(0, 0);
  assert r == 0;
}
