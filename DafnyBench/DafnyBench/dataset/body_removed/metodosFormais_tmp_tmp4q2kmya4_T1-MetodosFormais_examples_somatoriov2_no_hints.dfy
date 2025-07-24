function somaAteAberto(a:array<nat>, i:nat):nat
requires i <= a.Length
reads a
{}

method somatorio(a:array<nat>) returns (s:nat)
ensures s == somaAteAberto(a, a.Length)
{} 
