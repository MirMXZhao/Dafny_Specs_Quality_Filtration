// returns an index of the largest element of array 'a' in the range [0..n)
method findMax (a : array<int>, n : int) returns (r:int)
requires a.Length > 0
requires 0 < n <= a.Length
ensures 0 <= r < n <= a.Length;
ensures forall k :: 0 <= k < n <= a.Length ==> a[r] >= a[k];
ensures multiset(a[..]) == multiset(old(a[..]));
{}



method TestFindMax1() {
  var a := new int[5];
  a[0] := 3;
  a[1] := 7;
  a[2] := 1;
  a[3] := 9;
  a[4] := 5;
  var r := findMax(a, 4);
  assert r == 3;
}

method TestFindMax2() {
  var a := new int[3];
  a[0] := 10;
  a[1] := 2;
  a[2] := 8;
  var r := findMax(a, 2);
  assert r == 0;
}
