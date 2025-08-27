function Sum(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
decreases j
{}

predicate SumMaxToRight(v:array<int>,i:int,s:int)
reads v
requires 0<=i<v.Length
{}

method segMaxSum(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum(v,k,i+1) &&  SumMaxToRight(v,i,s)
{} 


function Sum2(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
decreases j-i
{}

predicate SumMaxToRight2(v:array<int>,j:int,i:int,s:int)
reads v
requires 0<=j<=i<v.Length
{}

method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
{}

////////TESTS////////

method TestsegMaxSum1() {
  var v := new int[4];
  v[0] := 1;
  v[1] := -3;
  v[2] := 2;
  v[3] := 1;
  var s, k := segMaxSum(v, 2);
  assert s == 3;
  assert k == 2;
}

method TestsegMaxSum2() {
  var v := new int[3];
  v[0] := 5;
  v[1] := -2;
  v[2] := 4;
  var s, k := segMaxSum(v, 1);
  assert s == 5;
  assert k == 0;
}

method TestsegSumaMaxima21() {
  var v := new int[4];
  v[0] := 1;
  v[1] := -3;
  v[2] := 2;
  v[3] := 1;
  var s, k := segSumaMaxima2(v, 2);
  assert s == 3;
  assert k == 2;
}

method TestsegSumaMaxima22() {
  var v := new int[3];
  v[0] := 5;
  v[1] := -2;
  v[2] := 4;
  var s, k := segSumaMaxima2(v, 1);
  assert s == 5;
  assert k == 0;
}
