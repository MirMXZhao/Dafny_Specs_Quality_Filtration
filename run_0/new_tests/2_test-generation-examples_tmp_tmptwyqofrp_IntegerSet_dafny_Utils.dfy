module Utils {
  class Assertions<T> {
    static method {:extern} assertEquals(expected : T, actual : T)
    requires expected == actual

    static method {:extern} expectEquals(expected : T, actual : T)
    ensures expected == actual

    static method {:extern} assertTrue(condition : bool)
    requires condition

    static method {:extern} expectTrue(condition : bool)
    ensures condition
    
    static method {:extern} assertFalse(condition : bool)
    requires !condition

    static method {:extern} expectFalse(condition : bool)
    ensures !condition
  }
}

////////TESTS////////

method TestBelowZero1() {
  var operations := [1, 2, -4, 5];
  var s, result := below_zero(operations);
  assert s.Length == 5;
  assert s[0] == 0;
  assert s[1] == 1;
  assert s[2] == 3;
  assert s[3] == -1;
  assert s[4] == 4;
  assert result == true;
}

method TestBelowZero2() {
  var operations := [1, 2, 3, 1];
  var s, result := below_zero(operations);
  assert s.Length == 5;
  assert s[0] == 0;
  assert s[1] == 1;
  assert s[2] == 3;
  assert s[3] == 6;
  assert s[4] == 7;
  assert result == false;
}
