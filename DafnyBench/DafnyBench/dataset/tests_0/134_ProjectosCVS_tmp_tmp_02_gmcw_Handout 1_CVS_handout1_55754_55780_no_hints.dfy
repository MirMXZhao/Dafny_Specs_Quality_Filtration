lemma peasantMultLemma(a:int, b:int)
    requires b >= 0
    ensures b % 2 == 0 ==> (a * b == 2 * a * b / 2)
    ensures b % 2 == 1 ==> (a * b == a + 2 * a * (b - 1) / 2)
    {}

method peasantMult(a: int, b: int) returns (r: int)
    requires b > 0
    ensures r == a * b
    {}

method euclidianDiv(a: int,b : int) returns (q: int,r: int)
    requires a >= 0
    requires b > 0
    ensures a == b * q + r
    {}

////////TESTS////////

method TestPeasantMult1() {
  var r := peasantMult(5, 3);
  assert r == 15;
}

method TestPeasantMult2() {
  var r := peasantMult(7, 4);
  assert r == 28;
}

method TestPeasantMult3() {
  var r := peasantMult(1, 1);
  assert r == 1;
}

method TestEuclidianDiv1() {
  var q, r := euclidianDiv(17, 5);
  assert q == 3;
  assert r == 2;
}

method TestEuclidianDiv2() {
  var q, r := euclidianDiv(20, 4);
  assert q == 5;
  assert r == 0;
}

method TestEuclidianDiv3() {
  var q, r := euclidianDiv(7, 3);
  assert q == 2;
  assert r == 1;
}
