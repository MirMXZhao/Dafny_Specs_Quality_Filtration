predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{}

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(i:nat) returns (result:bool)
  requires 1<i
  ensures result == IsPrime(i)
{}

method Main()
{}

