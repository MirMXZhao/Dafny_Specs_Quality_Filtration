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

method testFib1() {
  var r := Fib(0);
  assert r == fib(0);
}

method testFib2() {
  var r := Fib(5);
  assert r == fib(5);
}

method testFib3() {
  var r := Fib(1);
  assert r == fib(1);
}

method testaddImp1() {
  var r := addImp(Nil);
  assert r == add(Nil);
}

method testaddImp2() {
  var r := addImp(Cons(1, Cons(2, Cons(3, Nil))));
  assert r == add(Cons(1, Cons(2, Cons(3, Nil))));
}

method testaddImp3() {
  var r := addImp(Cons(-5, Cons(10, Nil)));
  assert r == add(Cons(-5, Cons(10, Nil)));
}

method testmaxArray1() {
  var arr := new int[3];
  arr[0] := 1;
  arr[1] := 5;
  arr[2] := 3;
  var max := maxArray(arr);
  assert forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max;
  assert exists x::0 <= x < arr.Length && arr[x] == max;
}

method testmaxArray2() {
  var arr := new int[1];
  arr[0] := 42;
  var max := maxArray(arr);
  assert forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max;
  assert exists x::0 <= x < arr.Length && arr[x] == max;
}

method testmaxArray3() {
  var arr := new int[3];
  arr[0] := -10;
  arr[1] := -5;
  arr[2] := -15;
  var max := maxArray(arr);
  assert forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max;
  assert exists x::0 <= x < arr.Length && arr[x] == max;
}

method testmaxArrayReverse1() {
  var arr := new int[4];
  arr[0] := 8;
  arr[1] := 2;
  arr[2] := 9;
  arr[3] := 1;
  var max := maxArrayReverse(arr);
  assert forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max;
  assert exists x::0 <= x < arr.Length && arr[x] == max;
}

method testmaxArrayReverse2() {
  var arr := new int[2];
  arr[0] := 7;
  arr[1] := 3;
  var max := maxArrayReverse(arr);
  assert forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max;
  assert exists x::0 <= x < arr.Length && arr[x] == max;
}

method testmaxArrayReverse3() {
  var arr := new int[5];
  arr[0] := 100;
  arr[1] := 200;
  arr[2] := 50;
  arr[3] := 150;
  arr[4] := 75;
  var max := maxArrayReverse(arr);
  assert forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max;
  assert exists x::0 <= x < arr.Length && arr[x] == max;
}

method testsumBackwards1() {
  var r := sumBackwards(0);
  assert r == sum(0);
}

method testsumBackwards2() {
  var r := sumBackwards(10);
  assert r == sum(10);
}

method testsumBackwards3() {
  var r := sumBackwards(3);
  assert r == sum(3);
}
