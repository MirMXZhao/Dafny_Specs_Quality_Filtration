predicate {:opaque} P(x:int)

method test(y:int)
    requires forall x :: P(x);
{
    assert P(y);
}