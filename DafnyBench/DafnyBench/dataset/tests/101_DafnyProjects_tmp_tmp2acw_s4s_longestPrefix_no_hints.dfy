method longestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
 ensures i <= a.Length && i <= b.Length
 ensures a[..i] == b[..i]
 ensures i < a.Length && i < b.Length ==> a[i] != b[i]
{}

////////TESTS////////

method TestLongestPrefix1() {
  var a := new int[4] [1, 2, 3, 4];
  var b := new int[4] [1, 2, 5, 6];
  var i := longestPrefix(a, b);
  assert i == 2;
}

method TestLongestPrefix2() {
  var a := new int[3] [7, 8, 9];
  var b := new int[2] [7, 8];
  var i := longestPrefix(a, b);
  assert i == 2;
}

method TestLongestPrefix3() {
  var a := new int[0] [];
  var b := new int[3] [1, 2, 3];
  var i := longestPrefix(a, b);
  assert i == 0;
}

method TestLongestPrefix4() {
  var a := new int[3] [1, 2, 3];
  var b := new int[3] [1, 2, 3];
  var i := longestPrefix(a, b);
  assert i == 3;
}
