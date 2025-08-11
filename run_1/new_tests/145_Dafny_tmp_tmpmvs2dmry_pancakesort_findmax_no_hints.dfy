method findMax (a : array<int>, n : int) returns (r:int)
requires a.Length > 0
requires 0 < n <= a.Length
ensures 0 <= r < n <= a.Length;
ensures forall k :: 0 <= k < n <= a.Length ==> a[r] >= a[k];
ensures multiset(a[..]) == multiset(old(a[..]));
{}

////////TESTS////////

method TestFindMax1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 7, 2, 9, 1;
  var r := findMax(a, 4);
  assert r == 3;
}

method TestFindMax2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 5, 2;
  var r := findMax(a, 2);
  assert r == 0 || r == 1;
}
