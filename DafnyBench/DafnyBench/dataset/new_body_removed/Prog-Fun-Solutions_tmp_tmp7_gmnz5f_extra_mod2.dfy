
ghost function f2(n: nat): nat {}

method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
{}
