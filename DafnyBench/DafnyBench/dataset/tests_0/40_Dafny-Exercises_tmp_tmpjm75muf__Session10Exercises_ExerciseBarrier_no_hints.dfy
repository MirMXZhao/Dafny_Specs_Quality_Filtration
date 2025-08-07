method barrier(v:array<int>,p:int) returns (b:bool)
requires v.Length > 0
requires 0<=p<v.Length
ensures b==forall k,l::0<=k<=p && p<l<v.Length ==> v[k]<v[l]
{}

////////TESTS////////

method TestBarrier1() {
  var v := new int[5];
  v[0] := 1;
  v[1] := 2;
  v[2] := 3;
  v[3] := 5;
  v[4] := 7;
  var b := barrier(v, 2);
  assert b == true;
}

method TestBarrier2() {
  var v := new int[4];
  v[0] := 1;
  v[1] := 3;
  v[2] := 2;
  v[3] := 4;
  var b := barrier(v, 1);
  assert b == false;
}

method TestBarrier3() {
  var v := new int[1];
  v[0] := 5;
  var b := barrier(v, 0);
  assert b == true;
}
