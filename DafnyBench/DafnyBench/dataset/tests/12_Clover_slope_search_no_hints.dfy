method SlopeSearch(a: array2<int>, key: int) returns (m:int, n:int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a[i,j]==key
  ensures 0<=m<a.Length0 && 0<=n<a.Length1
  ensures a[m,n]==key
{}

////////TESTS////////

method TestSlopeSearch1() {
  var a := new int[2,2];
  a[0,0] := 1; a[0,1] := 3;
  a[1,0] := 2; a[1,1] := 4;
  var m, n := SlopeSearch(a, 3);
  assert m == 0;
  assert n == 1;
}

method TestSlopeSearch2() {
  var a := new int[3,3];
  a[0,0] := 1; a[0,1] := 2; a[0,2] := 3;
  a[1,0] := 4; a[1,1] := 5; a[1,2] := 6;
  a[2,0] := 7; a[2,1] := 8; a[2,2] := 9;
  var m, n := SlopeSearch(a, 5);
  assert m == 1;
  assert n == 1;
}

method TestSlopeSearch3() {
  var a := new int[1,3];
  a[0,0] := 10; a[0,1] := 20; a[0,2] := 30;
  var m, n := SlopeSearch(a, 10);
  assert m == 0;
  assert n == 0;
}
