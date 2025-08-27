method Busca<T(==)>(a:array<T>, x:T) returns (r:int)
  ensures 0 <= r ==> r < a.Length && a[r] == x
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
{}

////////TESTS////////

method TestBusca1() {
  var a := new int[5];
  a[0] := 10;
  a[1] := 20;
  a[2] := 30;
  a[3] := 40;
  a[4] := 50;
  var r := Busca(a, 30);
  assert r == 2;
}

method TestBusca2() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 10;
  a[2] := 15;
  var r := Busca(a, 25);
  assert r < 0;
}
