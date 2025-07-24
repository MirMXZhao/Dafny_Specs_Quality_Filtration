method SlopeSearch(a: array2<int>, key: int) returns (m:int, n:int)
  requires forall i,j,j'::0<=i<a.Length0 && 0<=j<j'<a.Length1 ==> a[i,j]<=a[i,j']
  requires forall i,i',j::0<=i<i'<a.Length0 && 0<=j<a.Length1 ==> a[i,j]<=a[i',j]
  requires exists i,j :: 0<=i<a.Length0 && 0<=j<a.Length1 && a[i,j]==key
  ensures 0<=m<a.Length0 && 0<=n<a.Length1
  ensures a[m,n]==key
{}



method TestSlopeSearch1() {
  var a := new int[2,3];
  a[0,0] := 1; a[0,1] := 3; a[0,2] := 5;
  a[1,0] := 2; a[1,1] := 4; a[1,2] := 6;
  var m, n := SlopeSearch(a, 4);
  assert 0 <= m < a.Length0 && 0 <= n < a.Length1;
  assert a[m,n] == 4;
}

method TestSlopeSearch2() {
  var a := new int[3,2];
  a[0,0] := 1; a[0,1] := 2;
  a[1,0] := 3; a[1,1] := 4;
  a[2,0] := 5; a[2,1] := 6;
  var m, n := SlopeSearch(a, 1);
  assert 0 <= m < a.Length0 && 0 <= n < a.Length1;
  assert a[m,n] == 1;
}
