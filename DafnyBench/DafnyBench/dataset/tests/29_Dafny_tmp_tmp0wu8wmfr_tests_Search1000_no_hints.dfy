method Search1000( a: array<int>, x: int ) returns ( k: int )
    requires a.Length >= 1000;
    requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q];
    ensures 0 <= k <= 1000;
    ensures forall r | 0 <= r < k :: a[r] < x;
    ensures forall r | k <= r < 1000 :: a[r] >= x;
{}

predicate Is2Pow( n: int )
{}

method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
{}

method Search2PowRecursive( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
{}

////////TESTS////////

method TestSearch10001() {
  var a := new int[1000];
  var i := 0;
  while i < 1000 {
    a[i] := i;
    i := i + 1;
  }
  var k := Search1000(a, 500);
  assert k == 500;
}

method TestSearch10002() {
  var a := new int[1000];
  var i := 0;
  while i < 1000 {
    a[i] := 0;
    i := i + 1;
  }
  var k := Search1000(a, 1);
  assert k == 1000;
}

method TestSearch10003() {
  var a := new int[1000];
  var i := 0;
  while i < 1000 {
    a[i] := i * 2;
    i := i + 1;
  }
  var k := Search1000(a, -1);
  assert k == 0;
}

method TestSearch2PowLoop1() {
  var a := new int[8];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4; a[4] := 5; a[5] := 6; a[6] := 7; a[7] := 8;
  var k := Search2PowLoop(a, 0, 7, 5);
  assert k == 4;
}

method TestSearch2PowLoop2() {
  var a := new int[4];
  a[0] := 10; a[1] := 20; a[2] := 30; a[3] := 40;
  var k := Search2PowLoop(a, 0, 3, 25);
  assert k == 2;
}

method TestSearch2PowLoop3() {
  var a := new int[2];
  a[0] := 5; a[1] := 10;
  var k := Search2PowLoop(a, 0, 1, 3);
  assert k == 0;
}

method TestSearch2PowRecursive1() {
  var a := new int[8];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4; a[4] := 5; a[5] := 6; a[6] := 7; a[7] := 8;
  var k := Search2PowRecursive(a, 0, 7, 5);
  assert k == 4;
}

method TestSearch2PowRecursive2() {
  var a := new int[4];
  a[0] := 10; a[1] := 20; a[2] := 30; a[3] := 40;
  var k := Search2PowRecursive(a, 0, 3, 25);
  assert k == 2;
}

method TestSearch2PowRecursive3() {
  var a := new int[2];
  a[0] := 5; a[1] := 10;
  var k := Search2PowRecursive(a, 0, 1, 15);
  assert k == 2;
}
