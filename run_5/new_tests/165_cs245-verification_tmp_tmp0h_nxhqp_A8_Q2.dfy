method A8Q1(x: int, y: int, z: int) returns (m: int)
requires true;
ensures m<=x && m<=y && m<=z;
{}

////////TESTS////////

method TestA8Q11() {
  var m := A8Q1(5, 3, 7);
  assert m <= 5 && m <= 3 && m <= 7;
}

method TestA8Q12() {
  var m := A8Q1(-2, 10, 0);
  assert m <= -2 && m <= 10 && m <= 0;
}
