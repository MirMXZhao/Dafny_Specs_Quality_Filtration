function calcSum(n: nat) : nat 
{}

method sum(n: nat) returns(s: nat)
    ensures s == calcSum(n + 1)
{}
