function fib(n : nat) : nat
{}

method Fib(n : nat) returns (r:nat)
  ensures r == fib(n)
{}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l : List<int>) : int {}

method addImp(l : List<int>) returns (r: int)
  ensures r == add(l)
{}

method maxArray(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{}

method maxArrayReverse(arr : array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x::0 <= x < arr.Length && arr[x] == max
{}

function sum(n: nat) : nat
{}

method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
{}

////////TESTS////////

method TestFib1() {
  var r := Fib(5);
  assert r == fib(5);
}

method TestFib2() {
  var r := Fib(0);
  assert r == fib(0);
}

method TestaddImp1() {
  var l := Cons(1, Cons(2, Cons(3, Nil)));
  var r := addImp(l);
  assert r == add(l);
}

method TestaddImp2() {
  var l := Nil;
  var r := addImp(l);
  assert r == add(l);
}

method TestmaxArray1() {
  var arr := new int[3];
  arr[0] := 5;
  arr[1] := 2;
  arr[2] := 8;
  var max := maxArray(arr);
  assert max == 8;
}

method TestmaxArray2() {
  var arr := new int[1];
  arr[0] := 42;
  var max := maxArray(arr);
  assert max == 42;
}

method TestmaxArrayReverse1() {
  var arr := new int[4];
  arr[0] := 10;
  arr[1] := 3;
  arr[2] := 7;
  arr[3] := 1;
  var max := maxArrayReverse(arr);
  assert max == 10;
}

method TestmaxArrayReverse2() {
  var arr := new int[2];
  arr[0] := 15;
  arr[1] := 20;
  var max := maxArrayReverse(arr);
  assert max == 20;
}

method TestsumBackwards1() {
  var r := sumBackwards(4);
  assert r == sum(4);
}

method TestsumBackwards2() {
  var r := sumBackwards(10);
  assert r == sum(10);
}
