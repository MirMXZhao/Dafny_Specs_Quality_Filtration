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

////////TESTS////////

method Testmax1() {
  var z := max(5, 3);
  assert z == 5;
}

method Testmax2() {
  var z := max(2, 8);
  assert z == 8;
}

method Testmystery11() {
  var res := mystery1(3, 7);
  assert res == 10;
}

method Testmystery12() {
  var res := mystery1(5, 2);
  assert res == 7;
}

method Testmystery21() {
  var res := mystery2(4, 6);
  assert res == 24;
}

method Testmystery22() {
  var res := mystery2(3, 5);
  assert res == 15;
}

method Testm11() {
  var z := m1(2, 5);
  assert z == 0 || z == 1 || z == 3 || z == 4;
}

method Testm12() {
  var z := m1(1, 10);
  assert z >= 0 && z < 10 && z != 1;
}

method Testm31() {
  var z := m3(5, 5);
  assert z == true;
}

method Testm32() {
  var z := m3(3, 7);
  assert z == false || z == true;
}

method Testm41() {
  var z := m4(4, 4);
  assert z == true;
}

method Testm42() {
  var z := m4(2, 6);
  assert z == false;
}
