method Max (x: nat, y:nat) returns (r:nat)
    ensures (r >= x && r >=y)
    ensures (r == x || r == y)
{}

method m1 (x: int, y: int) returns (z: int)
requires 0 < x < y
ensures z >= 0 && z <= y && z != x
{}

function fib (n: nat) : nat
{}

method Fib (n: nat) returns (r:nat)
    ensures r == fib(n)
{}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l:List<int>) : int
{}

method addImp (l: List<int>) returns (s: int)
    ensures s == add(l)
{}

method MaxA (a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures exists i :: 0 <= i < a.Length && a[i] == m
{}

////////TESTS////////

method TestMax1() {
  var r := Max(5, 3);
  assert r == 5;
}

method TestMax2() {
  var r := Max(2, 7);
  assert r == 7;
}

method Testm11() {
  var z := m1(2, 5);
  assert z >= 0 && z <= 5 && z != 2;
}

method Testm12() {
  var z := m1(1, 10);
  assert z >= 0 && z <= 10 && z != 1;
}

method TestFib1() {
  var r := Fib(0);
  assert r == fib(0);
}

method TestFib2() {
  var r := Fib(3);
  assert r == fib(3);
}

method TestaddImp1() {
  var l := Nil;
  var s := addImp(l);
  assert s == add(l);
}

method TestaddImp2() {
  var l := Cons(1, Cons(2, Nil));
  var s := addImp(l);
  assert s == add(l);
}

method TestMaxA1() {
  var a := new int[3];
  a[0] := 1; a[1] := 5; a[2] := 3;
  var m := MaxA(a);
  assert forall i :: 0 <= i < a.Length ==> a[i] <= m;
  assert exists i :: 0 <= i < a.Length && a[i] == m;
}

method TestMaxA2() {
  var a := new int[2];
  a[0] := 7; a[1] := 2;
  var m := MaxA(a);
  assert forall i :: 0 <= i < a.Length ==> a[i] <= m;
  assert exists i :: 0 <= i < a.Length && a[i] == m;
}
