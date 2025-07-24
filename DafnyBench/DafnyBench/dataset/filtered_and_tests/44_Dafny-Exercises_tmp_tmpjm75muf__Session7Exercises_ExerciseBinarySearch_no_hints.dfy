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
 

 


method TestBinarySearch1() {
  var v := new int[5];
  v[0] := 1; v[1] := 3; v[2] := 5; v[3] := 7; v[4] := 9;
  var p := binarySearch(v, 5);
  assert p == 2;
}

method TestBinarySearch2() {
  var v := new int[4];
  v[0] := 2; v[1] := 4; v[2] := 6; v[3] := 8;
  var p := binarySearch(v, 3);
  assert p == 0;
}

method TestSearch1() {
  var v := new int[5];
  v[0] := 1; v[1] := 3; v[2] := 5; v[3] := 7; v[4] := 9;
  var b := search(v, 5);
  assert b == true;
}

method TestSearch2() {
  var v := new int[4];
  v[0] := 2; v[1] := 4; v[2] := 6; v[3] := 8;
  var b := search(v, 3);
  assert b == false;
}

method TestBinarySearchRec1() {
  var v := new int[5];
  v[0] := 1; v[1] := 3; v[2] := 5; v[3] := 7; v[4] := 9;
  var p := binarySearchRec(v, 5, 0, 4);
  assert p == 2;
}

method TestBinarySearchRec2() {
  var v := new int[4];
  v[0] := 2; v[1] := 4; v[2] := 6; v[3] := 8;
  var p := binarySearchRec(v, 1, 0, 3);
  assert p == -1;
}

method TestOtherbSearch1() {
  var v := new int[5];
  v[0] := 1; v[1] := 3; v[2] := 5; v[3] := 7; v[4] := 9;
  var b, p := otherbSearch(v, 5);
  assert b == true;
  assert p == 2;
}

method TestOtherbSearch2() {
  var v := new int[4];
  v[0] := 2; v[1] := 4; v[2] := 6; v[3] := 8;
  var b, p := otherbSearch(v, 3);
  assert b == false;
  assert p == 1;
}
