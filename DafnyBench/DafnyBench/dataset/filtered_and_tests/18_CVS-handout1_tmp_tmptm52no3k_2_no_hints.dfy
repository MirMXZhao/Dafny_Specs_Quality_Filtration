/*                                      Functional Lists and Imperative Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes        57854
*/

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

method Main() {}


method TestFromArray1() {
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

method TestFromArray2() {
  var a := new int[0];
  var l := from_array(a);
  assert length(l) == 0;
}
