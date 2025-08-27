predicate {:opaque} P(x:int)

method test(y:int)
    requires forall x :: P(x);
{
    assert P(y);
}

////////TESTS////////

method TestTest1() {
  test(5);
}

method TestTest2() {
  test(-3);
}
