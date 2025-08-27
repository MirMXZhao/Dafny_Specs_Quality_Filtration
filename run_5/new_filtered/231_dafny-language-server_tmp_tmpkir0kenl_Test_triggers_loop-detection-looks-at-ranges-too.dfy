predicate P(x: int)

method M(x: int) {
  assert true || forall x: int | P(x) :: P(x+1);
  assert true || forall x: int | P(x+1) :: P(x);
}