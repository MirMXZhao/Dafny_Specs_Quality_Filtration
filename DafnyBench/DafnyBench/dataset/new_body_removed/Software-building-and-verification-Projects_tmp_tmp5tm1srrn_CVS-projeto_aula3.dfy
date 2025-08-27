function fib(n : nat) : nat
{}

method Fib(n : nat) returns (r:nat)
  ensures r == fib(n)
{}

// 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l : List<int>) : int {}

method addImp(l : List<int>) returns (r: int)
  ensures r == add(l)
{}

// 3.
method maxArray(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{}

// 5.
method maxArrayReverse(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{}

// 6
function sum(n: nat) : nat
{}

method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
{}
