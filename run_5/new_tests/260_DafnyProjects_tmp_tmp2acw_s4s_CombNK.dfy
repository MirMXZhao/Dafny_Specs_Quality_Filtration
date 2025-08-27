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

method TestComb1() {
  var result := comb(5, 2);
  assert result == 10;
}

method TestComb2() {
  var result := comb(4, 0);
  assert result == 1;
}
