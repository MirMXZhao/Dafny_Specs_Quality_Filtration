method arraySum(a: array<int>, b: array<int>) returns (c: array<int> )
  requires a.Length==b.Length
  ensures c.Length==a.Length
  ensures forall i:: 0 <= i< a.Length==> a[i] + b[i]==c[i]
{}

////////TESTS////////

method TestArraySum1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var b := new int[3];
  b[0] := 4; b[1] := 5; b[2] := 6;
  var c := arraySum(a, b);
  assert c[0] == 5 && c[1] == 7 && c[2] == 9;
}

method TestArraySum2() {
  var a := new int[2];
  a[0] := -1; a[1] := 0;
  var b := new int[2];
  b[0] := 1; b[1] := -2;
  var c := arraySum(a, b);
  assert c[0] == 0 && c[1] == -2;
}
