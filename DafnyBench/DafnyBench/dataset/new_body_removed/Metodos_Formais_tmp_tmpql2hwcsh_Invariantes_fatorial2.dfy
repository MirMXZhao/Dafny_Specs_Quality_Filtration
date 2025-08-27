function Fat(n:nat):nat
{}

method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{}

// i | n | variante
// 1 | 3 | 2
// 2 | 3 | 1
// 3 | 3 | 0
// 4 | 3 | -1
// variante = n - i
// então é usado o decreases n-1
