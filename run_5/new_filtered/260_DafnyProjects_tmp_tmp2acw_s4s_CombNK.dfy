function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{}
by method
{}

lemma combProps(n: nat, k: nat)
   requires 0 <= k <= n
   ensures comb(n, k) == comb(n, n-k)
{}