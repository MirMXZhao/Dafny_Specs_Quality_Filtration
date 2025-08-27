predicate P(x: int)

method M(x: int) {
  assert true || forall x: int | P(x) :: P(x+1);
  assert true || forall x: int | P(x+1) :: P(x);
}

////////TESTS////////

method TestM1() {
  M(5);
}

method TestM2() {
  M(-3);
}
