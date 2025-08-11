method max(x:array<nat>) returns (y:nat) 
requires x.Length > 0
ensures forall j :: 0 <= j < x.Length ==> y >= x[j]
ensures y in x[..]
{}