method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q

{}

////////TESTS////////

method TestTorneo1() {
  var Valores := new real[20];
  Valores[0] := 5.0;
  Valores[1] := 3.0;
  Valores[2] := 7.0;
  var pos_padre, pos_madre := torneo(Valores, 0, 1, 2);
  assert pos_padre == 2;
  assert pos_madre == 0;
}

method TestTorneo2() {
  var Valores := new real[25];
  Valores[5] := 2.5;
  Valores[10] := 8.5;
  Valores[15] := 6.0;
  var pos_padre, pos_madre := torneo(Valores, 5, 10, 15);
  assert pos_padre == 10;
  assert pos_madre == 15;
}
