function exp(b: nat, n: nat): nat {}

lemma exp_sum(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{}

lemma exp_sum_auto(b: nat)
  ensures forall n1: nat, n2: nat :: exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{}

function bits(n: nat): seq<bool>
  decreases n
{}

function from_bits(s: seq<bool>): nat {}

lemma bits_from_bits(n: nat)
  ensures from_bits(bits(n)) == n
{
}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + exp(2, |s|) * (if b then 1 else 0)
{}

method fast_exp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
{}

////////TESTS////////

method TestFastExp1() {
  var r := fast_exp(2, 3);
  assert r == 8;
}

method TestFastExp2() {
  var r := fast_exp(5, 0);
  assert r == 1;
}
