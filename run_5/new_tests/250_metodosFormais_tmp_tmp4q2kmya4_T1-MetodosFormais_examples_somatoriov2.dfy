function somaAteAberto(a:array<nat>, i:nat):nat
requires i <= a.Length
reads a
{}

method somatorio(a:array<nat>) returns (s:nat)
ensures s == somaAteAberto(a, a.Length)
{}

////////TESTS////////

method TestSomatorio1() {
  var a := new nat[4];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 4;
  var s := somatorio(a);
  assert s == 10;
}

method TestSomatorio2() {
  var a := new nat[0];
  var s := somatorio(a);
  assert s == 0;
}
