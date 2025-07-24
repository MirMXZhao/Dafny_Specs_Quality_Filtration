function SomaAte(a:array<nat>, i:nat):nat
  requires 0 <= i <= a.Length
  reads a
{}

method Somatorio(a:array<nat>) returns (s:nat)
  ensures s == SomaAte(a,a.Length)
{}
