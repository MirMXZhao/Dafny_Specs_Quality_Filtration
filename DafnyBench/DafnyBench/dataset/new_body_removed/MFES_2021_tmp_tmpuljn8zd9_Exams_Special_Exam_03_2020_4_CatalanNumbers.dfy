function C(n: nat): nat 
    decreases n
{}

method calcC(n: nat) returns (res: nat)
    ensures res == C(n)
{}

