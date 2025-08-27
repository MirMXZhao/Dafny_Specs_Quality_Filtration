predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}


method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]
{}

////////TESTS////////

method TestMcontained1() {
  var v := new int[3];
  v[0] := 1; v[1] := 3; v[2] := 5;
  var w := new int[5];
  w[0] := 1; w[1] := 2; w[2] := 3; w[3] := 4; w[4] := 5;
  var b := mcontained(v, w, 3, 5);
  assert b == true;
}

method TestMcontained2() {
  var v := new int[3];
  v[0] := 1; v[1] := 3; v[2] := 7;
  var w := new int[4];
  w[0] := 1; w[1] := 2; w[2] := 3; w[3] := 5;
  var b := mcontained(v, w, 3, 4);
  assert b == false;
}
