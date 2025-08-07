function sum(X_val: array<int>, X_crd: array<nat>, v : array<int>, b : int, k : int) : (s : int)
  reads X_val, X_crd, v
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  {}


method SpMV(X_val: array<int>, X_crd: array<nat>, X_pos: array<nat>, v : array<int>) returns (y : array<int>)
  requires X_crd.Length >= 1 
  requires X_crd.Length == X_val.Length;
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j];
  requires forall i :: 0 <= i < X_crd.Length ==> X_crd[i] < v.Length
  requires forall i :: 0 <= i < X_pos.Length ==> X_pos[i] <= X_val.Length
  requires X_pos.Length >= 1
  ensures y.Length + 1 == X_pos.Length
  ensures forall i :: 0 <= i < y.Length ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
  {}

////////TESTS////////

method testsum1() {
  var X_val := new int[3];
  X_val[0] := 2; X_val[1] := 3; X_val[2] := 1;
  var X_crd := new nat[3];
  X_crd[0] := 0; X_crd[1] := 1; X_crd[2] := 0;
  var v := new int[2];
  v[0] := 5; v[1] := 7;
  var s := sum(X_val, X_crd, v, 0, 2);
  assert s == 31;
}

method testsum2() {
  var X_val := new int[2];
  X_val[0] := 4; X_val[1] := 6;
  var X_crd := new nat[2];
  X_crd[0] := 0; X_crd[1] := 1;
  var v := new int[2];
  v[0] := 2; v[1] := 3;
  var s := sum(X_val, X_crd, v, 1, 2);
  assert s == 18;
}

method testsum3() {
  var X_val := new int[3];
  X_val[0] := 1; X_val[1] := 2; X_val[2] := 3;
  var X_crd := new nat[3];
  X_crd[0] := 0; X_crd[1] := 1; X_crd[2] := 0;
  var v := new int[2];
  v[0] := 0; v[1] := 0;
  var s := sum(X_val, X_crd, v, 0, 0);
  assert s == 0;
}

method testSpMV1() {
  var X_val := new int[4];
  X_val[0] := 1; X_val[1] := 2; X_val[2] := 3; X_val[3] := 4;
  var X_crd := new nat[4];
  X_crd[0] := 0; X_crd[1] := 1; X_crd[2] := 0; X_crd[3] := 1;
  var X_pos := new nat[3];
  X_pos[0] := 0; X_pos[1] := 2; X_pos[2] := 4;
  var v := new int[2];
  v[0] := 5; v[1] := 6;
  var y := SpMV(X_val, X_crd, X_pos, v);
  assert y.Length == 2;
  assert y[0] == sum(X_val, X_crd, v, X_pos[0], X_pos[1]);
  assert y[1] == sum(X_val, X_crd, v, X_pos[1], X_pos[2]);
}

method testSpMV2() {
  var X_val := new int[3];
  X_val[0] := 2; X_val[1] := 1; X_val[2] := 3;
  var X_crd := new nat[3];
  X_crd[0] := 0; X_crd[1] := 1; X_crd[2] := 0;
  var X_pos := new nat[2];
  X_pos[0] := 0; X_pos[1] := 3;
  var v := new int[2];
  v[0] := 4; v[1] := 2;
  var y := SpMV(X_val, X_crd, X_pos, v);
  assert y.Length == 1;
  assert y[0] == sum(X_val, X_crd, v, X_pos[0], X_pos[1]);
}

method testSpMV3() {
  var X_val := new int[1];
  X_val[0] := 7;
  var X_crd := new nat[1];
  X_crd[0] := 0;
  var X_pos := new nat[2];
  X_pos[0] := 0; X_pos[1] := 1;
  var v := new int[1];
  v[0] := 3;
  var y := SpMV(X_val, X_crd, X_pos, v);
  assert y.Length == 1;
  assert y[0] == sum(X_val, X_crd, v, X_pos[0], X_pos[1]);
}
