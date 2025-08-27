method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
  decreases B
{}

method strategy<T>(P: set<T>, Special: T) returns (count: int)
  requires |P| > 1 && Special in P
  ensures count == |P| - 1
  decreases *
{}

////////TESTS////////

method TestCardinalitySubsetLt1() {
  var A := {1, 2};
  var B := {1, 2, 3, 4};
  CardinalitySubsetLt(A, B);
}

method TestCardinalitySubsetLt2() {
  var A := {};
  var B := {5, 10};
  CardinalitySubsetLt(A, B);
}

method TestStrategy1() {
  var P := {1, 2, 3, 4};
  var Special := 2;
  var count := strategy(P, Special);
  assert count == 3;
}

method TestStrategy2() {
  var P := {"a", "b", "c"};
  var Special := "b";
  var count := strategy(P, Special);
  assert count == 2;
}
