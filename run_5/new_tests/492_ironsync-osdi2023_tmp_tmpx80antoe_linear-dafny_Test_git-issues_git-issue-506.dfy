class F {}

////////TESTS////////

method TestBelowZero1() {
  var operations := [1, 2, -4, 5];
  var s, result := below_zero(operations);
  assert s[..] == [0, 1, 3, -1, 4];
  assert result == true;
}

method TestBelowZero2() {
  var operations := [1, 2, 3, 1];
  var s, result := below_zero(operations);
  assert s[..] == [0, 1, 3, 6, 7];
  assert result == false;
}
