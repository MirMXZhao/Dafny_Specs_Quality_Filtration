ghost function gcd(x:int,y:int):int
  requires x > 0 && y > 0 
{}


method gcdI(m:int, n:int) returns (d:int)
  requires  m > 0 && n > 0
  ensures   d == gcd(m,n) 
{}

ghost function gcd'(x:int,y:int):int
  requires x > 0 && y > 0
  decreases x+y,y
{}

////////TESTS////////

method TestGcdI1() {
  var d := gcdI(12, 8);
  assert d == 4;
}

method TestGcdI2() {
  var d := gcdI(15, 25);
  assert d == 5;
}
