function R(n: nat): nat {}

method calcR(n: nat) returns (r: nat)
    ensures r == R(n) 
{}
