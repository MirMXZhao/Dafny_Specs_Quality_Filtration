function Power(n: nat): nat {}

method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{}

method Max(a: array<nat>) returns (m: int)
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{}

method Cube(n: nat) returns (c: nat) 
    ensures c == n * n * n
{}

method IncrementMatrix(a: array2<int>)
    modifies a
    ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{}

method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{}

method DoubleArray(src: array<int>, dst: array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{}

method RotateLeft(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
    ensures a[a.Length -1] == old(a[0])
{}

method RotateRight(a: array)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
    ensures a[0] == old(a[a.Length-1])
{}

////////TESTS////////

method TestPower1() {
  var y := ComputePower(3);
  assert y == Power(3);
}

method TestPower2() {
  var y := ComputePower(0);
  assert y == Power(0);
}

method TestMax1() {
  var a := new nat[3];
  a[0] := 5; a[1] := 2; a[2] := 8;
  var m := Max(a);
  assert m == 8;
}

method TestMax2() {
  var a := new nat[0];
  var m := Max(a);
  assert m == 0;
}

method TestCube1() {
  var c := Cube(3);
  assert c == 27;
}

method TestCube2() {
  var c := Cube(0);
  assert c == 0;
}

method TestIncrementMatrix1() {
  var a := new int[2,2];
  a[0,0] := 1; a[0,1] := 2;
  a[1,0] := 3; a[1,1] := 4;
  IncrementMatrix(a);
  assert a[0,0] == 2 && a[0,1] == 3 && a[1,0] == 4 && a[1,1] == 5;
}

method TestIncrementMatrix2() {
  var a := new int[1,1];
  a[0,0] := 0;
  IncrementMatrix(a);
  assert a[0,0] == 1;
}

method TestCopyMatrix1() {
  var src := new int[2,2];
  var dst := new int[2,2];
  src[0,0] := 1; src[0,1] := 2;
  src[1,0] := 3; src[1,1] := 4;
  dst[0,0] := 0; dst[0,1] := 0;
  dst[1,0] := 0; dst[1,1] := 0;
  CopyMatrix(src, dst);
  assert dst[0,0] == 1 && dst[0,1] == 2 && dst[1,0] == 3 && dst[1,1] == 4;
}

method TestCopyMatrix2() {
  var src := new int[1,1];
  var dst := new int[1,1];
  src[0,0] := 5;
  dst[0,0] := 0;
  CopyMatrix(src, dst);
  assert dst[0,0] == 5;
}

method TestDoubleArray1() {
  var src := new int[3];
  var dst := new int[3];
  src[0] := 1; src[1] := 2; src[2] := 3;
  dst[0] := 0; dst[1] := 0; dst[2] := 0;
  DoubleArray(src, dst);
  assert dst[0] == 2 && dst[1] == 4 && dst[2] == 6;
}

method TestDoubleArray2() {
  var src := new int[1];
  var dst := new int[1];
  src[0] := 5;
  dst[0] := 0;
  DoubleArray(src, dst);
  assert dst[0] == 10;
}

method TestRotateLeft1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  RotateLeft(a);
  assert a[0] == 2 && a[1] == 3 && a[2] == 1;
}

method TestRotateLeft2() {
  var a := new int[2];
  a[0] := 5; a[1] := 7;
  RotateLeft(a);
  assert a[0] == 7 && a[1] == 5;
}

method TestRotateRight1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  RotateRight(a);
  assert a[0] == 3 && a[1] == 1 && a[2] == 2;
}

method TestRotateRight2() {
  var a := new int[2];
  a[0] := 5; a[1] := 7;
  RotateRight(a);
  assert a[0] == 7 && a[1] == 5;
}
