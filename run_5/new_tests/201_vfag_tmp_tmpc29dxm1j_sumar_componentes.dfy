method suma_componentes(V : array?<int>) returns (suma : int)
  requires V != null
  ensures  suma == suma_aux(V, 0)
{}

function suma_aux(V : array?<int>, n : int) : int
  requires V != null
  requires 0 <= n <= V.Length
  decreases V.Length - n
  reads V
{}

////////TESTS////////

method Testsuma_componentes1() {
  var V := new int[4];
  V[0] := 1; V[1] := 2; V[2] := 3; V[3] := 4;
  var suma := suma_componentes(V);
  assert suma == 10;
}

method Testsuma_componentes2() {
  var V := new int[3];
  V[0] := -1; V[1] := 5; V[2] := 2;
  var suma := suma_componentes(V);
  assert suma == 6;
}
