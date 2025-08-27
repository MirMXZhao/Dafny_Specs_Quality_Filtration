function expo(x:int, n:nat): int
requires n >= 0;
{}

lemma {:induction false} Expon23(n: nat)
requires n >= 0;
ensures ((expo(2, 3 * n) - expo(3, n))) % 5 == 0;
{}

////////TESTS////////

method TestExpon231() {
  var n := 0;
  var result1 := expo(2, 3 * n);
  var result2 := expo(3, n);
  assert result1 == 1;
  assert result2 == 1;
  assert ((result1 - result2) % 5) == 0;
}

method TestExpon232() {
  var n := 1;
  var result1 := expo(2, 3 * n);
  var result2 := expo(3, n);
  assert result1 == 8;
  assert result2 == 3;
  assert ((result1 - result2) % 5) == 0;
}
