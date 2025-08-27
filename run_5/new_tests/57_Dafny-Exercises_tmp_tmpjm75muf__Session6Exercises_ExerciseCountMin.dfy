function min(v:array<int>,i:int):int
decreases i
 reads v
 requires 1<=i<=v.Length
 ensures forall k::0<=k<i==> v[k]>=min(v,i)
 {}


function countMin(v:array<int>,x:int, i:int):int
decreases i
 reads v
  requires 0<=i<=v.Length
  ensures !(x in v[0..i]) ==> countMin(v,x,i)==0
  {}


 method mCountMin(v:array<int>) returns (c:int)
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
{}

////////TESTS////////

method TestmCountMin1() {
  var v := new int[4];
  v[0] := 3;
  v[1] := 1;
  v[2] := 1;
  v[3] := 2;
  var c := mCountMin(v);
  assert c == 2;
}

method TestmCountMin2() {
  var v := new int[3];
  v[0] := 5;
  v[1] := 5;
  v[2] := 5;
  var c := mCountMin(v);
  assert c == 3;
}
