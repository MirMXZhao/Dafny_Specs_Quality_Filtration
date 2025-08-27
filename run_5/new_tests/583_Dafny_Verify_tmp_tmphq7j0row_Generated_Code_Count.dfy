function has_count(v: int, a: array<int>, n: int): int
    reads a
    requires n >= 0 && n <= a.Length
{}


method count (v: int, a: array<int>, n: int) returns (r: int)
    requires n >= 0 && n <= a.Length;
    ensures has_count(v, a, n) == r;
{}

////////TESTS////////

method TestCount1() {
  var a := new int[4];
  a[0] := 3;
  a[1] := 1;
  a[2] := 3;
  a[3] := 2;
  var r := count(3, a, 4);
  assert r == 2;
}

method TestCount2() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 2;
  a[2] := 1;
  var r := count(5, a, 2);
  assert r == 0;
}
