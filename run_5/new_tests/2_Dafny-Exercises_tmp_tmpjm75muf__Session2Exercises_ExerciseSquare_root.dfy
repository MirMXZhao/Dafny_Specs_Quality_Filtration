method mroot1(n:int) returns (r:int)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}


method mroot2(n:int) returns (r:int)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}

method mroot3(n:int) returns (r:int)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{}

////////TESTS////////

method TestMroot11() {
  var r := mroot1(16);
  assert r == 4;
}

method TestMroot12() {
  var r := mroot1(15);
  assert r == 3;
}

method TestMroot21() {
  var r := mroot2(25);
  assert r == 5;
}

method TestMroot22() {
  var r := mroot2(10);
  assert r == 3;
}

method TestMroot31() {
  var r := mroot3(36);
  assert r == 6;
}

method TestMroot32() {
  var r := mroot3(8);
  assert r == 2;
}
