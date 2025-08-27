method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a.Length == N && (forall k :: 0 <= k && k < N ==> 0 <= a[k]);
  ensures sum <= N * max;
{}

////////TESTS////////

method TestM1() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  var sum, max := M(3, a);
  assert sum == 15;
  assert max == 8;
}

method TestM2() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 3;
  a[2] := 0;
  a[3] := 7;
  var sum, max := M(4, a);
  assert sum == 11;
  assert max == 7;
}
