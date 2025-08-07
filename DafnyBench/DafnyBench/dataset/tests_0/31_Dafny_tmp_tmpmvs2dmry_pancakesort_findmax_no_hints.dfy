method findMax (a : array<int>, n : int) returns (r:int)
requires a.Length > 0
requires 0 < n <= a.Length
ensures 0 <= r < n <= a.Length;
ensures forall k :: 0 <= k < n <= a.Length ==> a[r] >= a[k];
ensures multiset(a[..]) == multiset(old(a[..]));
{}

////////TESTS////////

method TestfindMax1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 7, 1, 9, 2;
  var r := findMax(a, 3);
  assert r == 1;
}

method TestfindMax2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 5, 2, 8, 1;
  var r := findMax(a, 4);
  assert r == 2;
}

method TestfindMax3() {
  var a := new int[1];
  a[0] := 42;
  var r := findMax(a, 1);
  assert r == 0;
}

method TestfindMax4() {
  var a := new int[6];
  a[0], a[1], a[2], a[3], a[4], a[5] := 1, 1, 1, 1, 1, 1;
  var r := findMax(a, 3);
  assert 0 <= r < 3;
}
