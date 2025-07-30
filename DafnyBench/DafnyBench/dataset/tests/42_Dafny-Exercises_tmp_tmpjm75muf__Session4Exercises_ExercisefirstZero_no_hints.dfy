method mfirstCero(v:array<int>) returns (i:int)
ensures 0 <=i<=v.Length
ensures forall j:: 0<=j<i ==> v[j]!=0 
ensures i!=v.Length ==> v[i]==0  
{}

////////TESTS////////

method TestmfirstCero1() {
  var v := new int[5];
  v[0] := 1;
  v[1] := 2;
  v[2] := 0;
  v[3] := 4;
  v[4] := 5;
  var i := mfirstCero(v);
  assert i == 2;
}

method TestmfirstCero2() {
  var v := new int[3];
  v[0] := 1;
  v[1] := 2;
  v[2] := 3;
  var i := mfirstCero(v);
  assert i == 3;
}

method TestmfirstCero3() {
  var v := new int[1];
  v[0] := 0;
  var i := mfirstCero(v);
  assert i == 0;
}
