function Sum(n:nat):nat
 
{}

method ComputeSum(n:nat) returns (s:nat)
    ensures s ==Sum(n)
{}

////////TESTS////////

method TestSum1() {
  var result := Sum(5);
  assert result == 15;
}

method TestSum2() {
  var result := Sum(0);
  assert result == 0;
}

method TestComputeSum1() {
  var s := ComputeSum(4);
  assert s == 10;
}

method TestComputeSum2() {
  var s := ComputeSum(3);
  assert s == 6;
}
