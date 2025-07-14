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
{
  var i := 0;
  r := 0;
  while i < |a|
  { 
    total_lemma (a, i);
    r := r + a[i];
    i := i + 1;
  }
}

