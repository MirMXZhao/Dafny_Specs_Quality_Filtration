predicate strictSorted(s : seq<int>) {}


method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]
{}

////////TESTS////////

method testmcontained1() {
  var v := new int[3];
  v[0] := 1; v[1] := 3; v[2] := 5;
  var w := new int[5];
  w[0] := 1; w[1] := 2; w[2] := 3; w[3] := 4; w[4] := 5;
  var b := mcontained(v, w, 3, 5);
  assert b == true;
}

method testmcontained2() {
  var v := new int[3];
  v[0] := 1; v[1] := 6; v[2] := 8;
  var w := new int[4];
  w[0] := 1; w[1] := 2; w[2] := 3; w[3] := 4;
  var b := mcontained(v, w, 2, 4);
  assert b == false;
}

method testmcontained3() {
  var v := new int[2];
  v[0] := 10; v[1] := 20;
  var w := new int[3];
  w[0] := 5; w[1] := 15; w[2] := 25;
  var b := mcontained(v, w, 0, 3);
  assert b == true;
}
