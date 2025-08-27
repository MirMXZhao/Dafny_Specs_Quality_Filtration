method max(a: int, b: int) returns (z: int)
  requires true
  ensures z >= a || z >= b
{}

method mystery1(n: nat,m: nat) returns (res: nat)
  ensures n+m == res
{}

method mystery2(n: nat,m: nat) returns (res: nat)
  ensures n*m == res
{}

method m1(x: int,y: int) returns (z: int)
  requires 0 < x < y
  ensures z >= 0 && z < y && z != x
{}

method m2(x: nat) returns (y: int)
  requires x <= -1
  ensures y > x && y < x
{}

method m3(x: int,y: int) returns (z: bool)
  ensures z ==> x==y
{}

method m4(x: int,y: int) returns (z: bool)
  ensures z ==> x==y && x==y ==> z
{}