// Author: Snorri Agnarsson, snorri@hi.is

// Search1000 is a Dafny version of a function shown
// by Jon Bentley in his old Programming Pearls
// column in CACM.  Surprisingly Dafny needs no help
// to verify the function.
method Search1000( a: array<int>, x: int ) returns ( k: int )
    requires a.Length >= 1000;
    requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q];
    ensures 0 <= k <= 1000;
    ensures forall r | 0 <= r < k :: a[r] < x;
    ensures forall r | k <= r < 1000 :: a[r] >= x;
{}

// Is2Pow(n) is true iff n==2^k for some k>=0.
predicate Is2Pow( n: int )
{}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
{}

// This method is a binary search that only works for array
// segments of size n == 2^k-1 for some k>=0.
method Search2PowRecursive( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
{}


method TestSearch1000_1() {
  var a := new int[1000];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7; a[4] := 9;
  forall i | 5 <= i < 1000 { a[i] := 10; }
  var k := Search1000(a, 6);
  assert k == 3;
}

method TestSearch1000_2() {
  var a := new int[1000];
  forall i | 0 <= i < 1000 { a[i] := i * 2; }
  var k := Search1000(a, 100);
  assert k == 50;
}

method TestSearch2PowLoop_1() {
  var a := new int[7];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7; a[4] := 9; a[5] := 11; a[6] := 13;
  var k := Search2PowLoop(a, 0, 7, 6);
  assert k == 3;
}

method TestSearch2PowLoop_2() {
  var a := new int[3];
  a[0] := 2; a[1] := 4; a[2] := 6;
  var k := Search2PowLoop(a, 0, 3, 5);
  assert k == 2;
}

method TestSearch2PowRecursive_1() {
  var a := new int[7];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7; a[4] := 9; a[5] := 11; a[6] := 13;
  var k := Search2PowRecursive(a, 0, 7, 6);
  assert k == 3;
}

method TestSearch2PowRecursive_2() {
  var a := new int[3];
  a[0] := 2; a[1] := 4; a[2] := 6;
  var k := Search2PowRecursive(a, 0, 3, 1);
  assert k == 0;
}
