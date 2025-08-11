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

method TestSpMV1() {
  var X_val := new int[4](i => [2, 3, 1, 4][i]);
  var X_crd := new nat[4](i => [0, 1, 0, 2][i]);
  var X_pos := new nat[3](i => [0, 2, 4][i]);
  var v := new int[3](i => [1, 2, 3][i]);
  var y := SpMV(X_val, X_crd, X_pos, v);
  assert y.Length == 2;
  assert y[0] == sum(X_val, X_crd, v, 0, 2);
  assert y[1] == sum(X_val, X_crd, v, 2, 4);
}

method TestSpMV2() {
  var X_val := new int[3](i => [5, 7, 2][i]);
  var X_crd := new nat[3](i => [1, 0, 1][i]);
  var X_pos := new nat[2](i => [0, 3][i]);
  var v := new int[2](i => [4, 6][i]);
  var y := SpMV(X_val, X_crd, X_pos, v);
  assert y.Length == 1;
  assert y[0] == sum(X_val, X_crd, v, 0, 3);
}
