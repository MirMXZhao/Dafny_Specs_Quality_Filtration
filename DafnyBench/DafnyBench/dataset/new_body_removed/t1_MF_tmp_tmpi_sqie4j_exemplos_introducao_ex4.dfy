function Fat(n: nat): nat
{}

method Fatorial(n:nat)  returns (r:nat)
  ensures r == Fat(n)
{}
