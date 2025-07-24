predicate sorted(s : seq<int>) {}

method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
 {}


 method search(v:array<int>,elem:int) returns (b:bool)
 requires sorted(v[0..v.Length])
ensures b==(elem in v[0..v.Length])
 //Implement by calling binary search function
 {}




//Recursive binary search

method {} binarySearchRec(v:array<int>, elem:int, c:int, f:int) returns (p:int)
 requires sorted(v[0..v.Length])
 requires 0<=c<=f+1<=v.Length//0<=c<=v.Length && -1<=f<v.Length && c<=f+1
 requires forall k::0<=k<c ==> v[k]<=elem
 requires forall k::f<k<v.Length ==> v[k]>elem
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
 {}
 
 


method otherbSearch(v:array<int>, elem:int) returns (b:bool,p:int)
 requires sorted(v[0..v.Length])
 ensures 0<=p<=v.Length
 ensures b == (elem in v[0..v.Length])
 ensures b ==> p<v.Length && v[p]==elem
 ensures !b ==> (forall u::0<=u<p ==> v[u]<elem) && 
               (forall w::p<=w<v.Length ==> v[w]>elem)
 //Implement and verify
 {}
 

 
