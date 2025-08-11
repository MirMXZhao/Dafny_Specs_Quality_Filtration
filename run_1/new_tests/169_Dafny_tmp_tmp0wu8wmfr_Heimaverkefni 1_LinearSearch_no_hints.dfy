method SearchRecursive( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
{}

method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
{}

////////TESTS////////

method TestSearchRecursive1() {
  var a := [1, 3, 5, 7, 9];
  var k := SearchRecursive(a, 0, 5, 5);
  assert k == 2;
}

method TestSearchRecursive2() {
  var a := [1, 3, 5, 7, 9];
  var k := SearchRecursive(a, 0, 5, 4);
  assert k == -1;
}

method TestSearchLoop1() {
  var a := [2, 4, 6, 8, 10];
  var k := SearchLoop(a, 1, 4, 8);
  assert k == 3;
}

method TestSearchLoop2() {
  var a := [2, 4, 6, 8, 10];
  var k := SearchLoop(a, 0, 3, 7);
  assert k == -1;
}
