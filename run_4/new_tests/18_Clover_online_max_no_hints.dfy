method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{}

////////TESTS////////

method TestOnlineMax1() {
  var a := new int[5];
  a[0] := 3; a[1] := 1; a[2] := 4; a[3] := 1; a[4] := 5;
  var m, p := onlineMax(a, 2);
  assert m == 3;
  assert p == 2;
}

method TestOnlineMax2() {
  var a := new int[4];
  a[0] := 2; a[1] := 5; a[2] := 1; a[3] := 3;
  var m, p := onlineMax(a, 1);
  assert m == 2;
  assert p == 3;
}
