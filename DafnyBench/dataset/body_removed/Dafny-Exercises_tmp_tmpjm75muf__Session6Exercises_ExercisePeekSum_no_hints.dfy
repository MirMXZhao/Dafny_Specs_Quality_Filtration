
 predicate isPeek(v:array<int>,i:int)
 reads v
 requires 0<=i<v.Length
 {}

 function peekSum(v:array<int>,i:int):int
 reads v
 requires 0<=i<=v.Length
 {}

 
 method mPeekSum(v:array<int>) returns (sum:int)
 requires  v.Length>0
 ensures sum==peekSum(v,v.Length)
 //Implement and verify an O(v.Length) algorithm to solve this problem
 {}
