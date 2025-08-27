predicate sorted (a:array<int>, start:int, end:int)      
 requires a!=null       
 requires 0<=start<=end<=a.Length       
 reads a       
 {}


method InsertionSort (a:array<int>)
requires a!=null && a.Length>1 
ensures sorted(a, 0, a.Length) 
modifies a
{}