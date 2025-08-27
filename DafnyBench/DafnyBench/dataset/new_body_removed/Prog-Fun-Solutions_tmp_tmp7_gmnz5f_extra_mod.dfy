ghost function f(n: nat): nat {}

method mod(n:nat) returns (a:nat) 
ensures a == f(n)
{}

