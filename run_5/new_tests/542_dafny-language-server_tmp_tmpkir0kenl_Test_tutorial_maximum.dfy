method Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
{}

lemma MaximumIsUnique(values: seq<int>, m1: int, m2: int)
  requires m1 in values && forall i | 0 <= i < |values| :: values[i] <= m1
  requires m2 in values && forall i | 0 <= i < |values| :: values[i] <= m2
  ensures m1 == m2 {}

////////TESTS////////

method TestMaximum1() {
  var values := [1, 5, 3, 9, 2];
  var max := Maximum(values);
  assert max == 9;
}

method TestMaximum2() {
  var values := [-3, -1, -5, -2];
  var max := Maximum(values);
  assert max == -1;
}
