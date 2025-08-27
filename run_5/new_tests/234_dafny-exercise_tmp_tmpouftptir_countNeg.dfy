function verifyNeg(a: array<int>, idx: int) : nat
reads a
requires 0 <= idx <= a.Length
{}

method CountNeg(a: array<int>) returns (cnt: nat) 
ensures cnt == verifyNeg(a, a.Length)
{}

////////TESTS////////

method TestCountNeg1() {
  var a := new int[4];
  a[0] := -1;
  a[1] := 2;
  a[2] := -3;
  a[3] := 4;
  var cnt := CountNeg(a);
  assert cnt == verifyNeg(a, a.Length);
}

method TestCountNeg2() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  var cnt := CountNeg(a);
  assert cnt == verifyNeg(a, a.Length);
}
