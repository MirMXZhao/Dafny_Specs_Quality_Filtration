predicate sorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}

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
 decreases f-c
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

method TestbinarySearch1() {
  var v := new int[5];
  v[0] := 1; v[1] := 3; v[2] := 5; v[3] := 7; v[4] := 9;
  var p := binarySearch(v, 5);
  assert p == 2;
}

method TestbinarySearch2() {
  var v := new int[4];
  v[0] := 2; v[1] := 4; v[2] := 6; v[3] := 8;
  var p := binarySearch(v, 3);
  assert p == 0;
}

method Testsearch1() {
  var v := new int[3];
  v[0] := 1; v[1] := 2; v[2] := 3;
  var b := search(v, 2);
  assert b == true;
}

method Testsearch2() {
  var v := new int[3];
  v[0] := 1; v[1] := 3; v[2] := 5;
  var b := search(v, 4);
  assert b == false;
}

method TestbinarySearchRec1() {
  var v := new int[4];
  v[0] := 2; v[1] := 4; v[2] := 6; v[3] := 8;
  var p := binarySearchRec(v, 6, 0, 3);
  assert p == 2;
}

method TestbinarySearchRec2() {
  var v := new int[3];
  v[0] := 1; v[1] := 3; v[2] := 5;
  var p := binarySearchRec(v, 2, 0, 2);
  assert p == 0;
}

method TestotherbSearch1() {
  var v := new int[4];
  v[0] := 1; v[1] := 3; v[2] := 5; v[3] := 7;
  var b, p := otherbSearch(v, 3);
  assert b == true;
  assert p == 1;
}

method TestotherbSearch2() {
  var v := new int[3];
  v[0] := 2; v[1] := 4; v[2] := 6;
  var b, p := otherbSearch(v, 5);
  assert b == false;
  assert p == 2;
}
