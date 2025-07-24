// flips (i.e., reverses) array elements in the range [0..num]
method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
// ensures multiset(a[..]) == old(multiset(a[..]))
{}



method TestFlip1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 1, 2, 3, 4;
  flip(a, 2);
  assert a[0] == 3;
  assert a[1] == 2;
  assert a[2] == 1;
  assert a[3] == 4;
}

method TestFlip2() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 5, 10, 15, 20, 25;
  flip(a, 3);
  assert a[0] == 20;
  assert a[1] == 15;
  assert a[2] == 10;
  assert a[3] == 5;
  assert a[4] == 25;
}
