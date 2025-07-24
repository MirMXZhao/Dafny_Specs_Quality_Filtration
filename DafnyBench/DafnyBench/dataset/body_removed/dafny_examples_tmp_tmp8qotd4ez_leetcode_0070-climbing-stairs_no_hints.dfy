function Stairs(n: nat): nat {}

// A simple specification
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
{}
