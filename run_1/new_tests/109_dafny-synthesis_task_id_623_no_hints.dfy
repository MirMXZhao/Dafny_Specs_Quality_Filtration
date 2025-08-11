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
  var l := [2, 3, 4];
  var n := 2;
  var result := PowerOfListElements(l, n);
  assert result == [4, 9, 16];
}

method TestPowerOfListElements2() {
  var l := [5, -2, 1];
  var n := 3;
  var result := PowerOfListElements(l, n);
  assert result == [125, -8, 1];
}
