method LucidNumbers(n: int) returns (lucid: seq<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
    ensures forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
{}

////////TESTS////////

method TestLucidNumbers1() {
  var lucid := LucidNumbers(10);
  assert lucid == [0, 3, 6, 9];
}

method TestLucidNumbers2() {
  var lucid := LucidNumbers(5);
  assert lucid == [0, 3];
}
