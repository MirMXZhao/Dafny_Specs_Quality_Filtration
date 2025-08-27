function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
    decreases j - i
{}

method query(a: array<int>, i: int, j: int) returns (res:int)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
{}

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    reads c, a
{}

lemma aux(a: array<int>, c: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    decreases j - i
    ensures forall k: int :: i <= k <= j ==> sum(a, i, k) + sum(a, k, j) == c[k] - c[i] + c[j] - c[k]
{}

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a,c)  
    ensures r == sum(a, i, j)
{}

////////TESTS////////

method TestQueryFast1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var c := new int[5];
  c[0] := 0; c[1] := 1; c[2] := 3; c[3] := 6; c[4] := 10;
  var r := queryFast(a, c, 1, 3);
  assert r == 5;
}

method TestQueryFast2() {
  var a := new int[3];
  a[0] := 5; a[1] := -2; a[2] := 7;
  var c := new int[4];
  c[0] := 0; c[1] := 5; c[2] := 3; c[3] := 10;
  var r := queryFast(a, c, 0, 2);
  assert r == 3;
}
