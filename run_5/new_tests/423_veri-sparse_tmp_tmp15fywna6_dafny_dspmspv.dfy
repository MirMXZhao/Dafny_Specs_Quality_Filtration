function sum(X_val : array<int>, X_crd : array<nat>,
             v_val : array<int>, v_crd : array<nat>, kX : nat, kV : nat, pX_end : nat, pV_end : nat) : (s : int) 
  reads X_val, X_crd
  requires X_val.Length == X_crd.Length
  requires pX_end <= X_crd.Length
  requires 0 <= kX <= X_crd.Length

  reads v_crd, v_val
  requires v_val.Length == v_crd.Length
  requires pV_end <= v_crd.Length
  requires 0 <= kV <= v_crd.Length

  decreases pX_end + pV_end - (kX + kV)
  {}

function min(x : nat, y : nat) : nat {}

predicate notin(y: nat, x : array<nat>) 
  reads x
{
  forall i :: 0 <= i < x.Length ==> y != x[i]
}

predicate notin_seq(y: nat, x : seq<nat>) 
{
  forall i :: 0 <= i < |x| ==> y != x[i]
}

function index_seq(x : nat, y: seq<nat>) : (i : nat)
  ensures i >= |y| ==> notin_seq(x, y)
  ensures i <  |y| ==> y[i] == x
{}

function index(x : nat, y: array<nat>) : (i : nat)
  reads y
  ensures i >= y.Length ==> notin(x, y)
  ensures i <  y.Length ==> y[i] == x
{}

method DSpMSpV(X_val : array<int>, X_crd : array<nat>, X_pos : array<nat>,
                                  X_crd1 : array<nat>, X_len: nat,
              v_val : array<int>, v_crd : array<nat>) returns (y : array<int>)
  requires X_pos.Length >= 1
  requires X_val.Length == X_crd.Length
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j];
  requires forall i :: 0 <= i < X_pos.Length ==> 0 <= X_pos[i] <= X_val.Length

  requires X_len >= X_crd1.Length
  requires forall i :: 0 <= i < X_crd1.Length ==> X_crd1[i] < X_len

  requires X_crd1.Length < X_pos.Length
  requires forall i, j :: 0 <= i < j < X_crd1.Length ==> X_crd1[i] < X_crd1[j]

  requires v_val.Length == v_crd.Length

  ensures y.Length == X_len
  ensures forall i :: 0 <= i < y.Length ==> 
    y[i] == 
      if index(i, X_crd1) < X_crd1.Length then 
        sum(X_val, X_crd, v_val, v_crd, X_pos[index(i, X_crd1)], 0, X_pos[index(i, X_crd1)+1], v_val.Length)
      else 0
  {}

////////TESTS////////

method TestDSpMSpV1() {
  var X_val := new int[3];
  X_val[0] := 1; X_val[1] := 2; X_val[2] := 3;
  var X_crd := new nat[3];
  X_crd[0] := 0; X_crd[1] := 1; X_crd[2] := 2;
  var X_pos := new nat[3];
  X_pos[0] := 0; X_pos[1] := 2; X_pos[2] := 3;
  var X_crd1 := new nat[2];
  X_crd1[0] := 0; X_crd1[1] := 2;
  var v_val := new int[2];
  v_val[0] := 5; v_val[1] := 6;
  var v_crd := new nat[2];
  v_crd[0] := 0; v_crd[1] := 1;
  var y := DSpMSpV(X_val, X_crd, X_pos, X_crd1, 4, v_val, v_crd);
  assert y.Length == 4;
}

method TestDSpMSpV2() {
  var X_val := new int[2];
  X_val[0] := 4; X_val[1] := 7;
  var X_crd := new nat[2];
  X_crd[0] := 0; X_crd[1] := 1;
  var X_pos := new nat[2];
  X_pos[0] := 0; X_pos[1] := 2;
  var X_crd1 := new nat[1];
  X_crd1[0] := 1;
  var v_val := new int[3];
  v_val[0] := 8; v_val[1] := 9; v_val[2] := 10;
  var v_crd := new nat[3];
  v_crd[0] := 0; v_crd[1] := 1; v_crd[2] := 2;
  var y := DSpMSpV(X_val, X_crd, X_pos, X_crd1, 3, v_val, v_crd);
  assert y.Length == 3;
}
