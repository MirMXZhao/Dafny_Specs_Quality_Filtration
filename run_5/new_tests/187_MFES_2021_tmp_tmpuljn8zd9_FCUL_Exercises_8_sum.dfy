function calcSum(n: nat) : nat 
{}

method sum(n: nat) returns(s: nat)
    ensures s == calcSum(n + 1)
{}

////////TESTS////////

method TestSum1() {
  var s := sum(5);
  assert s == calcSum(6);
}

method TestSum2() {
  var s := sum(0);
  assert s == calcSum(1);
}
