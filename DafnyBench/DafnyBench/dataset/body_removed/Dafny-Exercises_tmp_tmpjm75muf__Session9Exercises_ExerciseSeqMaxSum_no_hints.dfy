

function Sum(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
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
{}

//Now do the same but with a loop from right to left
predicate SumMaxToRight2(v:array<int>,j:int,i:int,s:int)//maximum sum stuck to the right
reads v
requires 0<=j<=i<v.Length
{}

method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
//Implement and verify
{}
