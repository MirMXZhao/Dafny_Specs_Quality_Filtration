


predicate strictSorted(s : seq<int>) {}


method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]//exists j :: 0 <= j < m && v[k] == w[j]
{}




method TestMcontained1() {
  var v := new int[3] [1, 3, 5];
  var w := new int[5] [1, 2, 3, 4, 5];
  var b := mcontained(v, w, 3, 5);
  assert b == true;
}

method TestMcontained2() {
  var v := new int[3] [1, 3, 7];
  var w := new int[4] [1, 2, 3, 5];
  var b := mcontained(v, w, 3, 4);
  assert b == false;
}
