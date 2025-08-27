function contains(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{}

function upper_bound(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{}

function is_max(m: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{}

method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
{}

////////TESTS////////

method TestMax1() {
  var a := new int[4];
  a[0] := 3;
  a[1] := 7;
  a[2] := 1;
  a[3] := 9;
  var max := max(a, 4);
  assert max == 9;
}

method TestMax2() {
  var a := new int[3];
  a[0] := -5;
  a[1] := -2;
  a[2] := -8;
  var max := max(a, 2);
  assert max == -2;
}
