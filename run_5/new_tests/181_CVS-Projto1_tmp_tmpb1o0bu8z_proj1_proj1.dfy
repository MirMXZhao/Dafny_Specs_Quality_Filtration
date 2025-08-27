function sum (a:array<int>, i:int, j:int) :int
decreases j
reads a
requires 0 <= i <= j <= a.Length
{}

method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j <= a.Length
ensures s == sum(a, i, j)
{}

lemma queryLemma(a:array<int>, i:int, j:int, k:int)
    requires 0 <= i <= k <= j <= a.Length
    ensures  sum(a,i,k) + sum(a,k,j) == sum(a,i,j)
{
}

method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
ensures r == sum(a, i,j)
{}

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
    a.Length + 1 == c.Length
    && c[0] == 0
    && forall j :: 1 <= j <= a.Length ==> c[j] == sum(a,0,j)
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
requires a.Length > 0
ensures forall j::0 <= j < a.Length ==> mem(a[j],l)
{}

function mem<T(==)> (x: T, l:List<T>) : bool
decreases l
{}

////////TESTS////////

method TestQuery1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var s := query(a, 1, 3);
  assert s == sum(a, 1, 3);
}

method TestQuery2() {
  var a := new int[3];
  a[0] := 5; a[1] := -2; a[2] := 7;
  var s := query(a, 0, 2);
  assert s == sum(a, 0, 2);
}

method TestQueryFast1() {
  var a := new int[3];
  a[0] := 1; a[1] := 3; a[2] := 2;
  var c := new int[4];
  c[0] := 0; c[1] := 1; c[2] := 4; c[3] := 6;
  var r := queryFast(a, c, 1, 3);
  assert r == sum(a, 1, 3);
}

method TestQueryFast2() {
  var a := new int[2];
  a[0] := 5; a[1] := -1;
  var c := new int[3];
  c[0] := 0; c[1] := 5; c[2] := 4;
  var r := queryFast(a, c, 0, 2);
  assert r == sum(a, 0, 2);
}

method TestFromArray1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var l := from_array(a);
  assert mem(1, l) && mem(2, l) && mem(3, l);
}

method TestFromArray2() {
  var a := new int[2];
  a[0] := 5; a[1] := 7;
  var l := from_array(a);
  assert mem(5, l) && mem(7, l);
}
