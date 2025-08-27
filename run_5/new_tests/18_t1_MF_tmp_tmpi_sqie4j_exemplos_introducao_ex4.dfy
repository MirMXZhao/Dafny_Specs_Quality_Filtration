function Fat(n: nat): nat
{}

method Fatorial(n:nat)  returns (r:nat)
  ensures r == Fat(n)
{}

////////TESTS////////

method TestFat1() {
  var result := Fat(5);
  assert result == 120;
}

method TestFat2() {
  var result := Fat(0);
  assert result == 1;
}

method TestFatorial1() {
  var r := Fatorial(4);
  assert r == 24;
}

method TestFatorial2() {
  var r := Fatorial(3);
  assert r == 6;
}
