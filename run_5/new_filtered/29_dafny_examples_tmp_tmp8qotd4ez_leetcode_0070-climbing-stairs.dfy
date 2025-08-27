function Stairs(n: nat): nat {}

method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
{}