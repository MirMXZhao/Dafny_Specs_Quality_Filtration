function pow(base: int, exponent: int): int
  requires exponent >= 0
  decreases exponent
{}

method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
  requires operators != [] && operands != [] && |operators| + 1 == |operands|
  requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
{}

////////TESTS////////

method TestDoAlgebra1() {
  var operators := ['+', '*'];
  var operands := [2, 3, 4];
  var result := do_algebra(operators, operands);
  assert result == 14;
}

method TestDoAlgebra2() {
  var operators := ['*', '+'];
  var operands := [2, 3, 4];
  var result := do_algebra(operators, operands);
  assert result == 10;
}
