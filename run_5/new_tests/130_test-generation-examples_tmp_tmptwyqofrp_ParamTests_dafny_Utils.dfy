module Utils {

    export 
        reveals Assertions
        provides Assertions.assertEquals

    class Assertions {
        static method {:axiom} assertEquals<T>(left : T, right : T)
        requires left == right

        static method {:axiom} assertTrue(value : bool)
        requires value

        static method {:axiom} assertFalse(value : bool)
        requires !value
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
