method Max (x: nat, y:nat) returns (r:nat)
    ensures (r >= x && r >=y)
    ensures (r == x || r == y)
{}

method Test ()
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

