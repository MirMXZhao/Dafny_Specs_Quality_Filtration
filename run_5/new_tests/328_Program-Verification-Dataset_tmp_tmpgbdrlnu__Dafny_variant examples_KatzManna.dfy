method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
  ensures proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91;
{}

method Gcd(x1: int, x2: int)
  requires 1 <= x1 && 1 <= x2;
{}

method Determinant(X: array2<int>, M: int) returns (z: int)
  requires 1 <= M;
  requires X != null && M == X.Length0 && M == X.Length1;
  modifies X;
{}

////////TESTS////////

method TestNinetyOne1() {
  var z := NinetyOne(105, true);
  assert z == 95;
}

method TestNinetyOne2() {
  var z := NinetyOne(85, true);
  assert z == 91;
}

method TestGcd1() {
  Gcd(12, 18);
}

method TestGcd2() {
  Gcd(7, 5);
}

method TestDeterminant1() {
  var X := new int[2, 2];
  X[0, 0] := 1; X[0, 1] := 2;
  X[1, 0] := 3; X[1, 1] := 4;
  var z := Determinant(X, 2);
  assert z == -2;
}

method TestDeterminant2() {
  var X := new int[1, 1];
  X[0, 0] := 5;
  var z := Determinant(X, 1);
  assert z == 5;
}
