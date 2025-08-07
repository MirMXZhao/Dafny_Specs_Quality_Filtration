function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
{}

method query(a: array<int>, i: int, j: int) returns (res : int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
{}

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c)
  ensures r == sum(a, i, j)
{}

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  reads c, a
{}

lemma proof(a: array<int>, i: int, j: int, k:int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
  ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{}

function mem<T(==)> (x: T, l: List<T>) : bool
{}

////////TESTS////////

method testsum1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var res := sum(a, 0, 2);
  assert res == 3;
}

method testsum2() {
  var a := new int[3];
  a[0] := 5; a[1] := -2; a[2] := 7;
  var res := sum(a, 1, 3);
  assert res == 5;
}

method testsum3() {
  var a := new int[5];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4; a[4] := 5;
  var res := sum(a, 2, 2);
  assert res == 0;
}

method testquery1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var res := query(a, 0, 2);
  assert res == 3;
}

method testquery2() {
  var a := new int[3];
  a[0] := 5; a[1] := -2; a[2] := 7;
  var res := query(a, 1, 3);
  assert res == 5;
}

method testquery3() {
  var a := new int[1];
  a[0] := 10;
  var res := query(a, 0, 1);
  assert res == 10;
}

method testqueryFast1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var c := new int[5];
  c[0] := 0; c[1] := 1; c[2] := 3; c[3] := 6; c[4] := 10;
  assume is_prefix_sum_for(a, c);
  var r := queryFast(a, c, 0, 2);
  assert r == 3;
}

method testqueryFast2() {
  var a := new int[3];
  a[0] := 5; a[1] := -2; a[2] := 7;
  var c := new int[4];
  c[0] := 0; c[1] := 5; c[2] := 3; c[3] := 10;
  assume is_prefix_sum_for(a, c);
  var r := queryFast(a, c, 1, 3);
  assert r == 5;
}

method testqueryFast3() {
  var a := new int[2];
  a[0] := 3; a[1] := 4;
  var c := new int[3];
  c[0] := 0; c[1] := 3; c[2] := 7;
  assume is_prefix_sum_for(a, c);
  var r := queryFast(a, c, 0, 0);
  assert r == 0;
}

method testfrom_array1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var l := from_array(a);
  assert mem(1, l);
  assert mem(2, l);
  assert mem(3, l);
}

method testfrom_array2() {
  var a := new int[2];
  a[0] := 5; a[1] := 7;
  var l := from_array(a);
  assert mem(5, l);
  assert mem(7, l);
}

method testfrom_array3() {
  var a := new int[0];
  var l := from_array(a);
  assert !mem(1, l);
}

method testmem1() {
  var l := Cons(1, Cons(2, Nil));
  var res := mem(1, l);
  assert res == true;
}

method testmem2() {
  var l := Cons(3, Cons(4, Nil));
  var res := mem(5, l);
  assert res == false;
}
