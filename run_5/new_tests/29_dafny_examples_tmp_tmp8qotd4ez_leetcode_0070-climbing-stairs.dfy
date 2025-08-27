function Stairs(n: nat): nat {}

method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
{}

////////TESTS////////

method TestClimbStairs1() {
  var r := ClimbStairs(3);
  assert r == Stairs(3);
}

method TestClimbStairs2() {
  var r := ClimbStairs(5);
  assert r == Stairs(5);
}
