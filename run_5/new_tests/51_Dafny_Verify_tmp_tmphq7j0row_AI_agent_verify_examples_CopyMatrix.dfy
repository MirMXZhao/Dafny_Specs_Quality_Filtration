method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j]) 
{}

////////TESTS////////

method TestCopyMatrix1() {
  var src := new int[2,2];
  src[0,0] := 1; src[0,1] := 2;
  src[1,0] := 3; src[1,1] := 4;
  var dst := new int[2,2];
  dst[0,0] := 0; dst[0,1] := 0;
  dst[1,0] := 0; dst[1,1] := 0;
  CopyMatrix(src, dst);
  assert dst[0,0] == 1 && dst[0,1] == 2 && dst[1,0] == 3 && dst[1,1] == 4;
}

method TestCopyMatrix2() {
  var src := new int[1,3];
  src[0,0] := 5; src[0,1] := 10; src[0,2] := 15;
  var dst := new int[1,3];
  dst[0,0] := 99; dst[0,1] := 99; dst[0,2] := 99;
  CopyMatrix(src, dst);
  assert dst[0,0] == 5 && dst[0,1] == 10 && dst[0,2] == 15;
}
