method PlusOne (x : int) returns (y : int)
    requires x >= 0
    ensures y > 0
{
    y := x+1;
}

method Swap (a : array?<int>, i : int, j : int)
    requires a != null && 0 <= i < a.Length && 0 <= j < a.Length
    modifies a
{}

method IntDiv (m : int, n : int) returns (d : int, r : int)
    requires n > 0
    ensures m == n * d + r && 0 <= r < n
{}

method ArraySum (a : array<int>, b : array<int>) returns (c : array<int>)
    requires a.Length == b.Length
    ensures c.Length == a.Length && 
        forall i : int :: 0 <= i < c.Length ==> c[i] == a[i] + b[i]
{}

method Euclid (m : int, n : int) returns (gcd : int)
    requires m > 1 && n > 1 && m >= n
    ensures gcd > 0 && gcd <= n && gcd <= m && m % gcd == 0 && n % gcd == 0
    

method IsSorted (a : array<int>) returns (isSorted : bool)
    ensures isSorted <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] <= a[j]
{}

method IsPrime (m : int) returns (isPrime : bool)
    requires m > 0
    ensures isPrime <==> (m > 1 && forall j : int :: 2 <= j < m ==> m % j != 0) 
{}

method Reverse (a : array<int>) returns (aRev : array<int>)
    ensures aRev.Length == a.Length
    ensures forall i : int :: 0 <= i < a.Length ==> a[i] == aRev[aRev.Length-i-1]
    ensures fresh(aRev)
{}

method NoDups (a : array<int>) returns (noDups : bool)
    requires forall j : int :: 0 < j < a.Length ==> a[j-1] <= a[j]
    ensures noDups <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] != a[j]
{}

////////TESTS////////

method TestPlusOne1() {
  var y := PlusOne(5);
  assert y == 6;
}

method TestPlusOne2() {
  var y := PlusOne(0);
  assert y == 1;
}

method TestIntDiv1() {
  var d, r := IntDiv(17, 5);
  assert d == 3;
  assert r == 2;
}

method TestIntDiv2() {
  var d, r := IntDiv(20, 4);
  assert d == 5;
  assert r == 0;
}

method TestArraySum1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var b := new int[3];
  b[0] := 4; b[1] := 5; b[2] := 6;
  var c := ArraySum(a, b);
  assert c.Length == 3;
  assert c[0] == 5 && c[1] == 7 && c[2] == 9;
}

method TestArraySum2() {
  var a := new int[2];
  a[0] := -1; a[1] := 10;
  var b := new int[2];
  b[0] := 3; b[1] := -5;
  var c := ArraySum(a, b);
  assert c.Length == 2;
  assert c[0] == 2 && c[1] == 5;
}

method TestEuclid1() {
  var gcd := Euclid(12, 8);
  assert gcd == 4;
}

method TestEuclid2() {
  var gcd := Euclid(15, 9);
  assert gcd == 3;
}

method TestIsSorted1() {
  var a := new int[4];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7;
  var isSorted := IsSorted(a);
  assert isSorted == true;
}

method TestIsSorted2() {
  var a := new int[3];
  a[0] := 5; a[1] := 2; a[2] := 8;
  var isSorted := IsSorted(a);
  assert isSorted == false;
}

method TestIsPrime1() {
  var isPrime := IsPrime(7);
  assert isPrime == true;
}

method TestIsPrime2() {
  var isPrime := IsPrime(8);
  assert isPrime == false;
}

method TestReverse1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var aRev := Reverse(a);
  assert aRev.Length == 3;
  assert aRev[0] == 3 && aRev[1] == 2 && aRev[2] == 1;
}

method TestReverse2() {
  var a := new int[2];
  a[0] := 5; a[1] := 9;
  var aRev := Reverse(a);
  assert aRev.Length == 2;
  assert aRev[0] == 9 && aRev[1] == 5;
}

method TestNoDups1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var noDups := NoDups(a);
  assert noDups == true;
}

method TestNoDups2() {
  var a := new int[3];
  a[0] := 2; a[1] := 2; a[2] := 5;
  var noDups := NoDups(a);
  assert noDups == false;
}
