method plus_one (x: int) returns (r:int)
  requires x >= 0;
  ensures r == x + 1;
{return x+1;}
method add_by_one (x:int, y:int) returns (r:int)
{}

////////TESTS////////

method TestPlusOne1() {
  var r := plus_one(5);
  assert r == 6;
}

method TestPlusOne2() {
  var r := plus_one(0);
  assert r == 1;
}

method TestAddByOne1() {
  var r := add_by_one(3, 7);
  assert r == 4;
}

method TestAddByOne2() {
  var r := add_by_one(10, 15);
  assert r == 11;
}
