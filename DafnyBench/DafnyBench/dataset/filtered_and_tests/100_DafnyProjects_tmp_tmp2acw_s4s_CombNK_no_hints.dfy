
/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial recursive definition of C(n, k), based on the Pascal equality.
function comb(n: nat, k: nat): nat 
  requires 0 <= k <= n
{}
by method
// Calculates C(n,k) iteratively in time O(k*(n-k)) and space O(n-k), 
// with dynamic programming.
{}

lemma combProps(n: nat, k: nat)
   requires 0 <= k <= n
   ensures comb(n, k) == comb(n, n-k)
{}

method Main()
{}

method testComb() {
}





method TestComb1() {
  var result := comb(5, 2);
  assert result == 10;
}

method TestComb2() {
  var result := comb(4, 0);
  assert result == 1;
}
