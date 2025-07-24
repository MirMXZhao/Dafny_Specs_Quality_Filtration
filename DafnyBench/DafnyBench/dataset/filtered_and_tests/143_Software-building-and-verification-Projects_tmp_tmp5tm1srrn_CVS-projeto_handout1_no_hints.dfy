// 1 a)

// [ai, aj[
function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
{}

// 1 b)
method query(a: array<int>, i: int, j: int) returns (res : int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
{}

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
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


// 2

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
  ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{}

function mem<T(==)> (x: T, l: List<T>) : bool
{}


method TestSum1() {
  var a := new int[5];
  a[0] := 1; a[1] := 10; a[2] := 3; a[3] := -4; a[4] := 5;
  var result := sum(a, 1, 3);
  assert result == 9;
}

method TestSum2() {
  var a := new int[3];
  a[0] := 2; a[1] := -1; a[2] := 4;
  var result := sum(a, 0, 2);
  assert result == 1;
}

method TestQuery1() {
  var a := new int[4];
  a[0] := 5; a[1] := -2; a[2] := 3; a[3] := 1;
  var res := query(a, 1, 4);
  assert res == 2;
}

method TestQuery2() {
  var a := new int[2];
  a[0] := 7; a[1] := -3;
  var res := query(a, 0, 1);
  assert res == 7;
}

method TestQueryFast1() {
  var a := new int[5];
  a[0] := 1; a[1] := 10; a[2] := 3; a[3] := -4; a[4] := 5;
  var c := new int[6];
  c[0] := 0; c[1] := 1; c[2] := 11; c[3] := 14; c[4] := 10; c[5] := 15;
  var r := queryFast(a, c, 1, 4);
  assert r == 9;
}

method TestQueryFast2() {
  var a := new int[3];
  a[0] := 2; a[1] := -5; a[2] := 3;
  var c := new int[4];
  c[0] := 0; c[1] := 2; c[2] := -3; c[3] := 0;
  var r := queryFast(a, c, 0, 2);
  assert r == -3;
}

method TestFromArray1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var l := from_array(a);
  assert mem(1, l);
  assert mem(2, l);
  assert mem(3, l);
}

method TestFromArray2() {
  var a := new string[2];
  a[0] := "hello"; a[1] := "world";
  var l := from_array(a);
  assert mem("hello", l);
  assert mem("world", l);
}
