module RussianMultiplication {
    
    export provides mult

    method mult(n0 : int, m0 : int) returns (res : int)
    ensures res == (n0 * m0);
    {}
}

////////TESTS////////

method TestMult1() {
  var res := RussianMultiplication.mult(5, 7);
  assert res == 35;
}

method TestMult2() {
  var res := RussianMultiplication.mult(-3, 4);
  assert res == -12;
}
