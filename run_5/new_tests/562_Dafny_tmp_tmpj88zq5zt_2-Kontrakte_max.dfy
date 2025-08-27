method max(a: array<int>, b: array<int>, i: int, j: int)
  returns (m: int)
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
  ensures  a[i] > b[j] ==> m == a[i]
  ensures  a[i] <= b[j] ==> m == b[j]
{}

////////TESTS////////

method TestMax1() {
  var a := new int[3];
  a[0] := 5; a[1] := 10; a[2] := 3;
  var b := new int[2];
  b[0] := 7; b[1] := 2;
  var m := max(a, b, 1, 0);
  assert m == 10;
}

method TestMax2() {
  var a := new int[2];
  a[0] := 4; a[1] := 6;
  var b := new int[3];
  b[0] := 8; b[1] := 3; b[2] := 9;
  var m := max(a, b, 0, 2);
  assert m == 9;
}
