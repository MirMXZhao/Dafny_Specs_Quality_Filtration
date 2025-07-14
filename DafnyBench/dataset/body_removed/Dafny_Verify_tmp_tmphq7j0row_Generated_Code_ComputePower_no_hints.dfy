function Power(n: nat): nat {}

method ComputePower(n: nat) returns (p: nat)
    ensures p == Power(n)
{}
