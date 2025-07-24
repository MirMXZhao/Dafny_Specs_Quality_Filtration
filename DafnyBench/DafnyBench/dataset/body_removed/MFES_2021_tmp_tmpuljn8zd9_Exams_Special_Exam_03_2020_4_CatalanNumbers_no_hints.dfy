function C(n: nat): nat 
{}

method calcC(n: nat) returns (res: nat)
    ensures res == C(n)
{}

