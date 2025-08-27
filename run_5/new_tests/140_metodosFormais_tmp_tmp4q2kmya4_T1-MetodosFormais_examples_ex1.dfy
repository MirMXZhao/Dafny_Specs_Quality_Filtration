method buscar(a:array<int>, x:int) returns (r:int)
ensures r < 0 ==> forall i :: 0 <= i <a.Length ==> a[i] != x
ensures 0 <= r < a.Length ==> a[r] == x
{}

////////TESTS////////

method TestBuscar1() {
  var a := new int[4] := [1, 3, 5, 7];
  var r := buscar(a, 5);
  assert r == 2;
}

method TestBuscar2() {
  var a := new int[3] := [2, 4, 6];
  var r := buscar(a, 1);
  assert r < 0;
}
