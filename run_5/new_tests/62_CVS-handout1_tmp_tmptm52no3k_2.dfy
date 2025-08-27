datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function length<T>(l: List<T>): nat
{}

predicate mem<T(==)> (l: List<T>, x: T)
{
  match l
  case Nil => false
  case Cons(h, t) => if(h == x) then true else mem(t, x)
}

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

method TestFromArray1() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  var l := from_array(a);
  assert l == Cons(1, Cons(2, Cons(3, Nil)));
}

method TestFromArray2() {
  var a := new int[0];
  var l := from_array(a);
  assert l == Nil;
}
