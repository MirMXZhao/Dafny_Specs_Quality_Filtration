function fusc(n: int): nat

lemma rule1()
  ensures fusc(0) == 0

lemma rule2()
  ensures fusc(1) == 1

lemma rule3(n:nat)
  ensures fusc(2*n) == fusc(n)

lemma rule4(n:nat)
  ensures fusc(2*n+1) == fusc(n) + fusc(n+1)


method ComputeFusc(N: int) returns (b: int)
  requires N >= 0 
  ensures b == fusc(N)
{}

////////TESTS////////

method TestComputeFusc1() {
  var b := ComputeFusc(0);
  assert b == 0;
}

method TestComputeFusc2() {
  var b := ComputeFusc(5);
  assert b == 3;
}

method TestComputeFusc3() {
  var b := ComputeFusc(1);
  assert b == 1;
}
