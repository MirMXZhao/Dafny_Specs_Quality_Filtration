method PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
    requires n >= 0
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
{}

function Power(base: int, exponent: int): int
    requires exponent >= 0
{}

////////TESTS////////

method TestPowerOfListElements1() {
  var l := [1, 2, 3, 4];
  var n := 2;
  var result := PowerOfListElements(l, n);
  assert result == [1, 4, 9, 16];
}

method TestPowerOfListElements2() {
  var l := [2, -3, 5];
  var n := 3;
  var result := PowerOfListElements(l, n);
  assert result == [8, -27, 125];
}

method TestPowerOfListElements3() {
  var l := [];
  var n := 5;
  var result := PowerOfListElements(l, n);
  assert result == [];
}

method TestPower1() {
  var result := Power(2, 3);
  assert result == 8;
}

method TestPower2() {
  var result := Power(-3, 2);
  assert result == 9;
}

method TestPower3() {
  var result := Power(5, 0);
  assert result == 1;
}
