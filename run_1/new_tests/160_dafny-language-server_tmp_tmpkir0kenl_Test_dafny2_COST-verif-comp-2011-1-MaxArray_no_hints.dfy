method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
{}

////////TESTS////////

method Testmax1() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 3;
  a[2] := 8;
  var x := max(a);
  assert x == 2;
}

method Testmax2() {
  var a := new int[4];
  a[0] := 10;
  a[1] := 2;
  a[2] := 7;
  a[3] := 10;
  var x := max(a);
  assert x == 0 || x == 3;
}
