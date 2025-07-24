ghost function gcd(x:int,y:int):int
  requires x > 0 && y > 0 
{}


method gcdI(m:int, n:int) returns (d:int)
  requires  m > 0 && n > 0
  ensures   d == gcd(m,n) 
{}

ghost function gcd'(x:int,y:int):int
  requires x > 0 && y > 0
{}

