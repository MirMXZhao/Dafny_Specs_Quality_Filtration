function max(x:nat, y:nat) : nat
{}

method slow_max(a: nat, b: nat) returns (z: nat)
  ensures z == max(a, b)
{}

////////TESTS////////

method test_slow_max1() {
  var z := slow_max(5, 3);
  assert z == 5;
}

method test_slow_max2() {
  var z := slow_max(2, 8);
  assert z == 8;
}
