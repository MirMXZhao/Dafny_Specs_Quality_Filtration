


method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
{}



method TestReplace1() {
  var v := new int[4];
  v[0], v[1], v[2], v[3] := 1, 2, 1, 3;
  replace(v, 1, 5);
  assert v[0] == 5 && v[1] == 2 && v[2] == 5 && v[3] == 3;
}

method TestReplace2() {
  var v := new int[3];
  v[0], v[1], v[2] := 4, 4, 4;
  replace(v, 7, 9);
  assert v[0] == 4 && v[1] == 4 && v[2] == 4;
}
