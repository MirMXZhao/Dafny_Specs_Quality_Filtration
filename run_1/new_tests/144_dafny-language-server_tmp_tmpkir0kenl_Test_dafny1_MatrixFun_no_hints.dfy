method MirrorImage<T>(m: array2<T>)
  modifies m
  ensures forall i,j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==>
            m[i,j] == old(m[i, m.Length1-1-j])
{}

method Flip<T>(m: array2<T>)
  requires m.Length0 == m.Length1
  modifies m
  ensures forall i,j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==> m[i,j] == old(m[j,i])
{}

method PrintMatrix<T>(m: array2<T>)
{}

////////TESTS////////

method TestMirrorImage1() {
  var m := new int[2,3];
  m[0,0] := 1; m[0,1] := 2; m[0,2] := 3;
  m[1,0] := 4; m[1,1] := 5; m[1,2] := 6;
  MirrorImage(m);
  assert m[0,0] == 3 && m[0,1] == 2 && m[0,2] == 1;
  assert m[1,0] == 6 && m[1,1] == 5 && m[1,2] == 4;
}

method TestMirrorImage2() {
  var m := new int[1,2];
  m[0,0] := 7; m[0,1] := 8;
  MirrorImage(m);
  assert m[0,0] == 8 && m[0,1] == 7;
}

method TestFlip1() {
  var m := new int[2,2];
  m[0,0] := 1; m[0,1] := 2;
  m[1,0] := 3; m[1,1] := 4;
  Flip(m);
  assert m[0,0] == 1 && m[0,1] == 3;
  assert m[1,0] == 2 && m[1,1] == 4;
}

method TestFlip2() {
  var m := new int[3,3];
  m[0,0] := 1; m[0,1] := 2; m[0,2] := 3;
  m[1,0] := 4; m[1,1] := 5; m[1,2] := 6;
  m[2,0] := 7; m[2,1] := 8; m[2,2] := 9;
  Flip(m);
  assert m[0,0] ==
