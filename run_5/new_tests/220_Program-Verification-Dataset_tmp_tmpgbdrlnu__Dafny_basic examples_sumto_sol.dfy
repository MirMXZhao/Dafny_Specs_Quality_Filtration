function sum_up_to (n: nat): nat
{}


method SumUpTo (n: nat) returns (r: nat)
  ensures r == sum_up_to (n);
{}

function total (a: seq<nat>) : nat
{}

lemma total_lemma (a: seq<nat>, i:nat) 
  requires |a| > 0;
  requires 0 <= i < |a|;
  ensures total (a[0..i]) + a[i] == total (a[0..i+1]);
{}

method Total (a: seq<nat>) returns (r:nat)
  ensures r == total (a[0..|a|]); 
{}

////////TESTS////////

method TestSumUpTo1() {
  var r := SumUpTo(5);
  assert r == sum_up_to(5);
}

method TestSumUpTo2() {
  var r := SumUpTo(0);
  assert r == sum_up_to(0);
}

method TestTotal1() {
  var r := Total([1, 2, 3, 4]);
  assert r == total([1, 2, 3, 4]);
}

method TestTotal2() {
  var r := Total([]);
  assert r == total([]);
}
