function{:opaque} f(x:int):int { x }

lemma L()
    ensures forall x:int :: f(x) == x
{}

////////TESTS////////

method Testf1() {
  var result := f(5);
  assert result == 5;
}

method Testf2() {
  var result := f(-3);
  assert result == -3;
}
