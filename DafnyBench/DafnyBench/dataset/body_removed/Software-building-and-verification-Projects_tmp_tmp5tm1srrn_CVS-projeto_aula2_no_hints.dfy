//PRE-CONDITIONS -> REQUIRES
//POST-CONDITIONS -> ENSURES

method max(a: int, b: int) returns (z: int)
  requires true
  ensures z >= a || z >= b
{}

method Main() {}

// 3
method mystery1(n: nat,m: nat) returns (res: nat)
  ensures n+m == res
{}

method mystery2(n: nat,m: nat) returns (res: nat)
  ensures n*m == res
{}

// 5a
method m1(x: int,y: int) returns (z: int)
  requires 0 < x < y
  ensures z >= 0 && z < y && z != x
{}

// 5b
method m2(x: nat) returns (y: int)
  requires x <= -1
  ensures y > x && y < x
{}

// 5c
// pode dar false e eles nao serem iguais
// 
method m3(x: int,y: int) returns (z: bool)
  ensures z ==> x==y
{}

// 5d
method m4(x: int,y: int) returns (z: bool)
  ensures z ==> x==y && x==y ==> z
{}
