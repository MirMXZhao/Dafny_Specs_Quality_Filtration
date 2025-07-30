datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function length<T>(l: List<T>): nat
{}

predicate mem<T(==)> (l: List<T>, x: T)
{}

function at<T>(l: List<T>, i: nat): T
  requires i < length(l)
{}

method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
  ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{}

////////TESTS////////

method test_from_array1() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  var l := from_array(a);
  assert length(l) == 3;
  assert at(l, 0) == 1;
  assert at(l, 1) == 2;
  assert at(l, 2) == 3;
}

method test_from_array2() {
  var a := new string[0];
  var l := from_array(a);
  assert length(l) == 0;
}

method test_from_array3() {
  var a := new int[1];
  a[0] := 42;
  var l := from_array(a);
  assert length(l) == 1;
  assert at(l, 0) == 42;
}
