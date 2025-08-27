method swap3(a: array<int>, h: int, i: int, j: int)
  modifies a
  requires 0 <= h < a.Length
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j && j != h && h != i;
  ensures a[h] == old(a[i]);
  ensures a[j] == old(a[h]);
  ensures a[i] == old(a[j]);
  ensures forall k: int :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k]); 
{}

////////TESTS////////

method Testswap31() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 10, 20, 30, 40, 50;
  swap3(a, 0, 1, 2);
  assert a[0] == 20;
  assert a[1] == 30;
  assert a[2] == 10;
  assert a[3] == 40;
  assert a[4] == 50;
}

method Testswap32() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 100, 200, 300, 400;
  swap3(a, 2, 0, 3);
  assert a[0] == 300;
  assert a[1] == 200;
  assert a[2] == 100;
  assert a[3] == 400;
}
