method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
{}

////////TESTS////////

method testreplace1() {
  var v := new int[4];
  v[0] := 1; v[1] := 2; v[2] := 1; v[3] := 3;
  replace(v, 1, 5);
  assert v[0] == 5;
  assert v[1] == 2;
  assert v[2] == 5;
  assert v[3] == 3;
}

method testreplace2() {
  var v := new int[3];
  v[0] := 4; v[1] := 7; v[2] := 9;
  replace(v, 6, 8);
  assert v[0] == 4;
  assert v[1] == 7;
  assert v[2] == 9;
}

method testreplace3() {
  var v := new int[0];
  replace(v, 1, 2);
}
