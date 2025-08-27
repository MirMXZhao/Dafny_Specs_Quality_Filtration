method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{}

method mmaximum2(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{}

method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
{}

method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: i<l<v.Length ==> v[i]>v[l]
{}

method mmaxvalue1(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{}

method mmaxvalue2(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{}

////////TESTS////////

method testmmaximum11() {
  var v := new int[3];
  v[0] := 5; v[1] := 2; v[2] := 8;
  var i := mmaximum1(v);
  assert i == 2;
}

method testmmaximum12() {
  var v := new int[4];
  v[0] := 1; v[1] := 9; v[2] := 3; v[3] := 9;
  var i := mmaximum1(v);
  assert i == 1 || i == 3;
}

method testmmaximum21() {
  var v := new int[3];
  v[0] := 7; v[1] := 3; v[2] := 7;
  var i := mmaximum2(v);
  assert i == 0 || i == 2;
}

method testmmaximum22() {
  var v := new int[2];
  v[0] := 4; v[1] := 6;
  var i := mmaximum2(v);
  assert i == 1;
}

method testmfirstMaximum1() {
  var v := new int[4];
  v[0] := 3; v[1] := 7; v[2] := 7; v[3] := 2;
  var i := mfirstMaximum(v);
  assert i == 1;
}

method testmfirstMaximum2() {
  var v := new int[3];
  v[0] := 9; v[1] := 5; v[2] := 1;
  var i := mfirstMaximum(v);
  assert i == 0;
}

method testmlastMaximum1() {
  var v := new int[4];
  v[0] := 2; v[1] := 8; v[2] := 8; v[3] := 1;
  var i := mlastMaximum(v);
  assert i == 2;
}

method testmlastMaximum2() {
  var v := new int[3];
  v[0] := 1; v[1] := 5; v[2] := 9;
  var i := mlastMaximum(v);
  assert i == 2;
}

method testmmaxvalue11() {
  var v := new int[3];
  v[0] := 4; v[1] := 8; v[2] := 2;
  var m := mmaxvalue1(v);
  assert m == 8;
}

method testmmaxvalue12() {
  var v := new int[4];
  v[0] := 6; v[1] := 1; v[2] := 6; v[3] := 3;
  var m := mmaxvalue1(v);
  assert m == 6;
}

method testmmaxvalue21() {
  var v := new int[2];
  v[0] := 5; v[1] := 7;
  var m := mmaxvalue2(v);
  assert m == 7;
}

method testmmaxvalue22() {
  var v := new int[3];
  v[0] := 3; v[1] := 3; v[2] := 1;
  var m := mmaxvalue2(v);
  assert m == 3;
}
