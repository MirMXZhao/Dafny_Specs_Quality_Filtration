method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;

{}

method SearchLoop( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j;
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
{}

////////TESTS////////

method TestSearchRecursive1() {
  var a := [5.0, 3.0, 1.0];
  var k := SearchRecursive(a, 0, 3, 2.0);
  assert k == 2;
}

method TestSearchRecursive2() {
  var a := [10.0, 8.0, 6.0, 4.0];
  var k := SearchRecursive(a, 0, 4, 7.0);
  assert k == 1;
}

method TestSearchLoop1() {
  var a := [9.0, 7.0, 5.0, 3.0];
  var k := SearchLoop(a, 0, 4, 6.0);
  assert k == 2;
}

method TestSearchLoop2() {
  var a := [4.0, 2.0, 1.0];
  var k := SearchLoop(a, 0, 3, 0.5);
  assert k == 3;
}
