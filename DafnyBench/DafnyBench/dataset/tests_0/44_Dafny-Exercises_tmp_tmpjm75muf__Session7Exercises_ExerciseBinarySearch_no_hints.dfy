predicate sorted(s : seq<int>) {}

method binarySearch(v:array<int>, elem:int) returns (p:int)
 requires sorted(v[0..v.Length])
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
 {}


 method search(v:array<int>,elem:int) returns (b:bool)
 requires sorted(v[0..v.Length])
ensures b==(elem in v[0..v.Length])
 {}




method binarySearchRec(v:array<int>, elem:int, c:int, f:int) returns (p:int)
 requires sorted(v[0..v.Length])
 requires 0<=c<=f+1<=v.Length
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
 {}

////////TESTS////////

method testbinarySearch1() {
  var v := new int[4] := [1, 3, 5, 7];
  var p := binarySearch(v, 3);
  assert p == 1;
}

method testbinarySearch2() {
  var v := new int[4] := [1, 3, 5, 7];
  var p := binarySearch(v, 6);
  assert p == 2;
}

method testbinarySearch3() {
  var v := new int[1] := [5];
  var p := binarySearch(v, 5);
  assert p == 0;
}

method testsearch1() {
  var v := new int[4] := [1, 3, 5, 7];
  var b := search(v, 3);
  assert b == true;
}

method testsearch2() {
  var v := new int[4] := [1, 3, 5, 7];
  var b := search(v, 6);
  assert b == false;
}

method testsearch3() {
  var v := new int[0] := [];
  var b := search(v, 1);
  assert b == false;
}

method testbinarySearchRec1() {
  var v := new int[4] := [1, 3, 5, 7];
  var p := binarySearchRec(v, 3, 0, 3);
  assert p == 1;
}

method testbinarySearchRec2() {
  var v := new int[4] := [1, 3, 5, 7];
  var p := binarySearchRec(v, 6, 0, 3);
  assert p == 2;
}

method testbinarySearchRec3() {
  var v := new int[3] := [2, 4, 6];
  var p := binarySearchRec(v, 1, 0, 2);
  assert p == -1;
}

method testotherbSearch1() {
  var v := new int[4] := [1, 3, 5, 7];
  var b, p := otherbSearch(v, 3);
  assert b == true;
  assert p == 1;
}

method testotherbSearch2() {
  var v := new int[4] := [1, 3, 5, 7];
  var b, p := otherbSearch(v, 6);
  assert b == false;
  assert p == 3;
}

method testotherbSearch3() {
  var v := new int[2] := [10, 20];
  var b, p := otherbSearch(v, 5);
  assert b == false;
  assert p == 0;
}
