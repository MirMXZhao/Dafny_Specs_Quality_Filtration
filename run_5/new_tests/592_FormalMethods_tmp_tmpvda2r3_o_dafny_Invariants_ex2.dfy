function Potencia(x:nat, y:nat):nat
{}

method Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x,y)
{}

////////TESTS////////

method TestPot1() {
  var r := Pot(2, 3);
  assert r == 8;
}

method TestPot2() {
  var r := Pot(5, 0);
  assert r == 1;
}
