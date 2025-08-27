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