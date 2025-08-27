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

////////TESTS////////

method TestRoundDown1() {
  var rounding := new Rounding;
  rounding.thresholds := new int[3];
  rounding.thresholds[0] := 10;
  rounding.thresholds[1] := 20;
  rounding.thresholds[2] := 30;
  assume rounding.Valid();
  var r := rounding.RoundDown(25);
  assert r == 1;
}

method TestRoundDown2() {
  var rounding := new Rounding;
  rounding.thresholds := new int[3];
  rounding.thresholds[0] := 10;
  rounding.thresholds[1] := 20;
  rounding.thresholds[2] := 30;
  assume rounding.Valid();
  var r := rounding.RoundDown(5);
  assert r == -1;
}

method TestRoundUp1() {
  var rounding := new Rounding;
  rounding.thresholds := new int[3];
  rounding.thresholds[0] := 10;
  rounding.thresholds[1] := 20;
  rounding.thresholds[2] := 30;
  assume rounding.Valid();
  var r := rounding.RoundUp(15);
  assert r == 1;
}

method TestRoundUp2() {
  var rounding := new Rounding;
  rounding.thresholds := new int[3];
  rounding.thresholds[0] := 10;
  rounding.thresholds[1] := 20;
  rounding.thresholds[2] := 30;
  assume rounding.Valid();
  var r := rounding.RoundUp(35);
  assert r == 3;
}
