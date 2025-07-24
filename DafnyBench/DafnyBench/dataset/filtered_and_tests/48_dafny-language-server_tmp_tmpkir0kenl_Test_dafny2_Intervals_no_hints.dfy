// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The RoundDown and RoundUp methods in this file are the ones in the Boogie
// implementation Source/AbsInt/IntervalDomain.cs.

class Rounding {
  var thresholds: array<int>

  function Valid(): bool
    reads this, thresholds
  {}

  method RoundDown(k: int) returns (r: int)
    requires Valid()
    ensures -1 <= r < thresholds.Length
    ensures forall m :: r < m < thresholds.Length ==> k < thresholds[m]
    ensures 0 <= r ==> thresholds[r] <= k
  {}

  method RoundUp(k: int) returns (r: int)
    requires Valid()
    ensures 0 <= r <= thresholds.Length
    ensures forall m :: 0 <= m < r ==> thresholds[m] < k
    ensures r < thresholds.Length ==> k <= thresholds[r]
  {}
}



method TestRoundDown1() {
  var rounding := new Rounding;
  rounding.thresholds := new int[][10, 20, 30, 40, 50];
  assume rounding.Valid();
  var r := rounding.RoundDown(25);
  assert r == 1;
}

method TestRoundDown2() {
  var rounding := new Rounding;
  rounding.thresholds := new int[][5, 15, 25, 35];
  assume rounding.Valid();
  var r := rounding.RoundDown(3);
  assert r == -1;
}

method TestRoundUp1() {
  var rounding := new Rounding;
  rounding.thresholds := new int[][10, 20, 30, 40, 50];
  assume rounding.Valid();
  var r := rounding.RoundUp(25);
  assert r == 2;
}

method TestRoundUp2() {
  var rounding := new Rounding;
  rounding.thresholds := new int[][5, 15, 25, 35];
  assume rounding.Valid();
  var r := rounding.RoundUp(60);
  assert r == 4;
}
