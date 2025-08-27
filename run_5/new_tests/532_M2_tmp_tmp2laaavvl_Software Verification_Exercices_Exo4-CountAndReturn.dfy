method CountToAndReturnN(n: int) returns (r: int)
    requires n >= 0
    ensures r == n 
{}

////////TESTS////////

method TestCountToAndReturnN1() {
  var r := CountToAndReturnN(5);
  assert r == 5;
}

method TestCountToAndReturnN2() {
  var r := CountToAndReturnN(0);
  assert r == 0;
}
