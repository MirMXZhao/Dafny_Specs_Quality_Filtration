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
  var values := [1, 8, 7, 4, 5];
  var max := Maximum(values);
  assert max == 8;
}

method TestMaximum2() {
  var values := [-10, -5, -8, -3];
  var max := Maximum(values);
  assert max == -3;
}
