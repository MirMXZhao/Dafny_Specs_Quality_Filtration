method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
{}

////////TESTS////////

method Testreplace1() {
  var v := new int[4] [3, 1, 3, 2];
  replace(v, 3, 5);
  assert v[0] == 5;
  assert v[1] == 1;
  assert v[2] == 5;
  assert v[3] == 2;
}

method Testreplace2() {
  var v := new int[3] [1, 2, 1];
  replace(v, 4, 7);
  assert v[0] == 1;
  assert v[1] == 2;
  assert v[2] == 1;
}
