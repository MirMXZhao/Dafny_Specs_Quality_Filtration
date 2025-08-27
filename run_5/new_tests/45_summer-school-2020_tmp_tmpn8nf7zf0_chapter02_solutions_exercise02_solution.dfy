predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{
  && 1<i
  && ( forall f :: 1 < f < i ==> !divides(f, i) )
}

method test_prime(i:nat) returns (result:bool)
  requires 1<i
  ensures result == IsPrime(i)
{}

////////TESTS////////

method TestTestPrime1() {
  var result := test_prime(7);
  assert result == true;
}

method TestTestPrime2() {
  var result := test_prime(8);
  assert result == false;
}
