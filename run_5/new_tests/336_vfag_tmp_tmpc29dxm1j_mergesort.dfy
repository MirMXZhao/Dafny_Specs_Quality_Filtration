method ordenar_mergesort(V : array?<int>)
    requires V != null
    modifies V
{}

method mergesort(V : array?<int>, c : int, f : int) 
    requires V != null
    requires c >= 0 && f <= V.Length
    decreases f - c
    modifies V
{}

method mezclar(V: array?<int>, c : int, m : int, f : int)
    requires V != null
    requires c <= m <= f
    requires 0 <= c <= V.Length
    requires 0 <= m <= V.Length
    requires 0 <= f <= V.Length
    modifies V
{}

////////TESTS////////

method TestOrdenarMergesort1() {
  var V := new int[4];
  V[0] := 3; V[1] := 1; V[2] := 4; V[3] := 2;
  ordenar_mergesort(V);
}

method TestOrdenarMergesort2() {
  var V := new int[3];
  V[0] := 5; V[1] := 2; V[2] := 8;
  ordenar_mergesort(V);
}

method TestMergesort1() {
  var V := new int[4];
  V[0] := 3; V[1] := 1; V[2] := 4; V[3] := 2;
  mergesort(V, 0, 4);
}

method TestMergesort2() {
  var V := new int[5];
  V[0] := 9; V[1] := 3; V[2] := 7; V[3] := 1; V[4] := 5;
  mergesort(V, 1, 4);
}

method TestMezclar1() {
  var V := new int[6];
  V[0] := 1; V[1] := 3; V[2] := 5; V[3] := 2; V[4] := 4; V[5] := 6;
  mezclar(V, 0, 3, 6);
}

method TestMezclar2() {
  var V := new int[4];
  V[0] := 2; V[1] := 4; V[2] := 1; V[3] := 3;
  mezclar(V, 0, 2, 4);
}
