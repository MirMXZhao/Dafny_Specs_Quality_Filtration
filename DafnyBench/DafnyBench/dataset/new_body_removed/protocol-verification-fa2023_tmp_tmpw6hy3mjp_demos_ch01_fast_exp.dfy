function exp(b: nat, n: nat): nat {}

lemma exp_sum(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{}

// this "auto" version of exp_sum is convenient when we want to let Z3 figure
// out how to use exp_sum rather than providing all the arguments ourselves
lemma exp_sum_auto(b: nat)
  ensures forall n1: nat, n2: nat :: exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{}

/* A key aspect of this proof is that each iteration handles one bit of the
 * input. The best way I found to express its loop invariants is to compute and
 * refer to this sequence of bits, even if the code never materializes it. */

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

