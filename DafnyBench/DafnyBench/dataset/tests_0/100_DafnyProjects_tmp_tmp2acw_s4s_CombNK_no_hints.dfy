function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{}
by method
{}

lemma combProps(n: nat, k: nat)
   requires 0 <= k <= n
   ensures comb(n, k) == comb(n, n-k)
{}

////////TESTS////////

method testcomb1() {
  var result := comb(5, 2);
  assert result == 10;
}

method testcomb2() {
  var result := comb(4, 0);
  assert result == 1;
}

method testcomb3() {
  var result := comb(6, 6);
  assert result == 1;
}

method testcomb4() {
  var result := comb(7, 3);
  assert result == 35;
}

method testcombProps1() {
  combProps(5, 2);
  assert comb(5, 2) == comb(5, 3);
}

method testcombProps2() {
  combProps(4, 0);
  assert comb(4, 0) == comb(4, 4);
}
