function F(n: nat): nat {}

method calcF(n: nat) returns (res: nat)  
 ensures res == F(n) 
{}
