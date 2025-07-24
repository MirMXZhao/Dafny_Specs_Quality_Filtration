
method mfirstCero(v:array<int>) returns (i:int)
ensures 0 <=i<=v.Length
ensures forall j:: 0<=j<i ==> v[j]!=0 
ensures i!=v.Length ==> v[i]==0  
{}


method TestFirstCero1() {
  var v := new int[5];
  v[0] := 1; v[1] := 3; v[2] := 0; v[3] := 5; v[4] := 7;
  var i := mfirstCero(v);
  assert i == 2;
}

method TestFirstCero2() {
  var v := new int[4];
  v[0] := 1; v[1] := 2; v[2] := 3; v[3] := 4;
  var i := mfirstCero(v);
  assert i == 4;
}
