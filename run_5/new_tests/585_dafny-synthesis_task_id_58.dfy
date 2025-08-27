method HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{}

////////TESTS////////

method TestHasOppositeSign1() {
  var result := HasOppositeSign(-5, 3);
  assert result == true;
}

method TestHasOppositeSign2() {
  var result := HasOppositeSign(4, 7);
  assert result == false;
}
