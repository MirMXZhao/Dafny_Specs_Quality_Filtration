method Gauss(n:int) returns (sum:int)
requires n >= 0
ensures sum == n*(n+1)/2
{}

method sumOdds(n:nat) returns (sum:nat)
ensures sum == n*n;
{}

////////TESTS////////

method TestGauss1() {
  var sum := Gauss(5);
  assert sum == 15;
}

method TestGauss2() {
  var sum := Gauss(0);
  assert sum == 0;
}

method TestSumOdds1() {
  var sum := sumOdds(3);
  assert sum == 9;
}

method TestSumOdds2() {
  var sum := sumOdds(0);
  assert sum == 0;
}
