method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
{}

////////TESTS////////

method testmax1() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 3;
  a[2] := 8;
  var x := max(a);
  assert x == 2;
}

method testmax2() {
  var a := new int[4];
  a[0] := 10;
  a[1] := 2;
  a[2] := 7;
  a[3] := 10;
  var x := max(a);
  assert x == 0 || x == 3;
}

method testmax3() {
  var a := new int[1];
  a[0] := 42;
  var x := max(a);
  assert x == 0;
}
