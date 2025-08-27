method IncrementMatrix(a: array2<int>)
    modifies a
    ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{}

////////TESTS////////

method TestIncrementMatrix1() {
  var a := new int[2,2];
  a[0,0] := 1; a[0,1] := 2;
  a[1,0] := 3; a[1,1] := 4;
  var old_a := new int[2,2];
  old_a[0,0] := a[0,0]; old_a[0,1] := a[0,1];
  old_a[1,0] := a[1,0]; old_a[1,1] := a[1,1];
  IncrementMatrix(a);
  assert a[0,0] == old_a[0,0] + 1;
  assert a[0,1] == old_a[0,1] + 1;
  assert a[1,0] == old_a[1,0] + 1;
  assert a[1,1] == old_a[1,1] + 1;
}

method TestIncrementMatrix2() {
  var a := new int[1,3];
  a[0,0] := -5; a[0,1] := 0; a[0,2] := 10;
  var old_a := new int[1,3];
  old_a[0,0] := a[0,0]; old_a[0,1] := a[0,1]; old_a[0,2] := a[0,2];
  IncrementMatrix(a);
  assert a[0,0] == old_a[0,0] + 1;
  assert a[0,1] == old_a[0,1] + 1;
  assert a[0,2] == old_a[0,2] + 1;
}
