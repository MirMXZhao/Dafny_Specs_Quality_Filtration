function max(x:nat, y:nat) : nat
{}

method slow_max(a: nat, b: nat) returns (z: nat)
  ensures z == max(a, b)
{}

