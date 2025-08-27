function even(n: int): bool
  requires n >= 0
{}

method is_even(n: int) returns (r: bool)
  requires n >= 0;
  ensures r <==> even(n);
{}

////////TESTS////////

method Testeven1() {
  var result := even(4);
  assert result == true;
}

method Testeven2() {
  var result := even(7);
  assert result == false;
}

method Testis_even1() {
  var r := is_even(6);
  assert r == true;
}

method Testis_even2() {
  var r := is_even(9);
  assert r == false;
}
