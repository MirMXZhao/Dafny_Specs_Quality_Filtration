method RotateRight(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
    ensures a[0] == old(a[a.Length-1])
{}


method TestRotateRight1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  RotateRight(a);
  assert a[0] == 4;
  assert a[1] == 1;
  assert a[2] == 2;
  assert a[3] == 3;
}

method TestRotateRight2() {
  var a := new int[3];
  a[0] := 10; a[1] := 20; a[2] := 30;
  RotateRight(a);
  assert a[0] == 30;
  assert a[1] == 10;
  assert a[2] == 20;
}
