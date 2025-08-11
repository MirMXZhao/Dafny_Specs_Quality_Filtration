method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
{}

////////TESTS////////

method TestFlip1() {
  var a := new int[5] [1, 2, 3, 4, 5];
  flip(a, 2);
  assert a[0] == 3 && a[1] == 2 && a[2] == 1 && a[3] == 4 && a[4] == 5;
}

method TestFlip2() {
  var a := new int[4] [10, 20, 30, 40];
  flip(a, 3);
  assert a[0] == 40 && a[1] == 30 && a[2] == 20 && a[3] == 10;
}
