method UpdateElements(a: array<int>)
  requires a.Length >= 8
  modifies a
  ensures old(a[4]) +3 == a[4]
  ensures a[7]==516
  ensures forall i::0 <= i<a.Length ==> i != 7 && i != 4 ==> a[i] == old(a[i])
{}

////////TESTS////////

method TestUpdateElements1() {
  var a := new int[8];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7] := 10, 20, 30, 40, 50, 60, 70, 80;
  UpdateElements(a);
  assert a[0] == 10;
  assert a[1] == 20;
  assert a[2] == 30;
  assert a[3] == 40;
  assert a[4] == 53;
  assert a[5] == 60;
  assert a[6] == 70;
  assert a[7] == 516;
}

method TestUpdateElements2() {
  var a := new int[10];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9] := 1, 2, 3, 4, 5, 6, 7, 8, 9, 10;
  UpdateElements(a);
  assert a[0] == 1;
  assert a[1] == 2;
  assert a[2] == 3;
  assert a[3] == 4;
  assert a[4] == 8;
  assert a[5] == 6;
  assert a[6] == 7;
  assert a[7] == 516;
  assert a[8] == 9;
  assert a[9] == 10;
}
