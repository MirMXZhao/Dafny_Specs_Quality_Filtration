function min(v:array<int>,i:int):int
 reads v
 requires 1<=i<=v.Length
 ensures forall k::0<=k<i==> v[k]>=min(v,i)
 {}


function countMin(v:array<int>,x:int, i:int):int
 reads v
  requires 0<=i<=v.Length
  ensures !(x in v[0..i]) ==> countMin(v,x,i)==0
  {}





 method mCountMin(v:array<int>) returns (c:int)
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
//Implement and verify an O(v.Length) algorithm 
{}
