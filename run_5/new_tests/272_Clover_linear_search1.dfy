method LinearSearch(a: array<int>, e: int) returns (n:int)
  ensures 0<=n<=a.Length
  ensures n==a.Length || a[n]==e
  ensures forall i::0<=i < n ==> e!=a[i]
{}

////////TESTS////////

method TestLinearSearch1() {
  var a := new int[4];
  a[0] := 3; a[1] := 7; a[2] := 1; a[3] := 9;
  var n := LinearSearch(a, 7);
  assert n == 1;
}

method TestLinearSearch2() {
  var a := new int[3];
  a[0] := 2; a[1] := 5; a[2] := 8;
  var n := LinearSearch(a, 10);
  assert n == 3;
}
