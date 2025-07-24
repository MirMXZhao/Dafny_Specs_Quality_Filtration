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


method TestFib1() {
  var r := Fib(5);
  assert r == fib(5);
}

method TestFib2() {
  var r := Fib(0);
  assert r == fib(0);
}

method TestAddImp1() {
  var l := Cons(1, Cons(2, Cons(3, Nil)));
  var r := addImp(l);
  assert r == add(l);
}

method TestAddImp2() {
  var l := Nil;
  var r := addImp(l);
  assert r == add(l);
}

method TestMaxArray1() {
  var arr := new int[3];
  arr[0] := 5;
  arr[1] := 2;
  arr[2] := 8;
  var max := maxArray(arr);
  assert max >= 5 && max >= 2 && max >= 8;
  assert max == 5 || max == 2 || max == 8;
}

method TestMaxArray2() {
  var arr := new int[1];
  arr[0] := 42;
  var max := maxArray(arr);
  assert max == 42;
}

method TestMaxArrayReverse1() {
  var arr := new int[4];
  arr[0] := 3;
  arr[1] := 7;
  arr[2] := 1;
  arr[3] := 9;
  var max := maxArrayReverse(arr);
  assert max >= 3 && max >= 7 && max >= 1 && max >= 9;
  assert max == 3 || max == 7 || max == 1 || max == 9;
}

method TestMaxArrayReverse2() {
  var arr := new int[2];
  arr[0] := -5;
  arr[1] := -10;
  var max := maxArrayReverse(arr);
  assert max >= -5 && max >= -10;
  assert max == -5 || max == -10;
}

method TestSumBackwards1() {
  var r := sumBackwards(4);
  assert r == sum(4);
}

method TestSumBackwards2() {
  var r := sumBackwards(0);
  assert r == sum(0);
}
