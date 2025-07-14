// problem 6:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXXX

ghost function f(n: int): int {}

ghost function fSum(n: nat): int {}

method problem6(n:nat) returns (a: int)
ensures a == fSum(n)
{}

