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

method testRoundDown1() {
  var rounding := new Rounding;
  rounding.thresholds := new int[4];
  rounding.thresholds[0] := 10;
  rounding.thresholds[1] := 20;
  rounding.thresholds[2] := 30;
  rounding.thresholds[3] := 40;
  assume rounding.Valid();
  var r := rounding.RoundDown(25);
  assert r == 1;
}

method testRoundDown2() {
  var rounding := new Rounding;
  rounding.thresholds := new int[3];
  rounding.thresholds[0] := 5;
  rounding.thresholds[1] := 15;
  rounding.thresholds[2] := 25;
  assume rounding.Valid();
  var r := rounding.RoundDown(3);
  assert r == -1;
}

method testRoundDown3() {
  var rounding := new Rounding;
  rounding.thresholds := new int[2];
  rounding.thresholds[0] := 10;
  rounding.thresholds[1] := 20;
  assume rounding.Valid();
  var r := rounding.RoundDown(20);
  assert r == 1;
}

method testRoundUp1() {
  var rounding := new Rounding;
  rounding.thresholds := new int[4];
  rounding.thresholds[0] := 10;
  rounding.thresholds[1] := 20;
  rounding.thresholds[2] := 30;
  rounding.thresholds[3] := 40;
  assume rounding.Valid();
  var r := rounding.RoundUp(25);
  assert r == 2;
}

method testRoundUp2() {
  var rounding := new Rounding;
  rounding.thresholds := new int[3];
  rounding.thresholds[0] := 5;
  rounding.thresholds[1] := 15;
  rounding.thresholds[2] := 25;
  assume rounding.Valid();
  var r := rounding.RoundUp(30);
  assert r == 3;
}

method testRoundUp3() {
  var rounding := new Rounding;
  rounding.thresholds := new int[2];
  rounding.thresholds[0] := 10;
  rounding.thresholds[1] := 20;
  assume rounding.Valid();
  var r := rounding.RoundUp(5);
  assert r == 0;
}
