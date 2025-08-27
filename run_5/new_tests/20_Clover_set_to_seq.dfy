method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  ensures multiset(s) == multiset(xs)
{}

////////TESTS////////

method TestSetToSeq1() {
  var s := {1, 2, 3};
  var xs := SetToSeq(s);
  assert multiset(s) == multiset(xs);
}

method TestSetToSeq2() {
  var s := {"a", "b"};
  var xs := SetToSeq(s);
  assert multiset(s) == multiset(xs);
}
