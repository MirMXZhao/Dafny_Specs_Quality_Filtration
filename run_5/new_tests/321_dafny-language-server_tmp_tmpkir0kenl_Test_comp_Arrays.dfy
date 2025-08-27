method LinearSearch(a: array<int>, key: int) returns (n: nat)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == key
{}

method PrintArray<A>(a: array?<A>) {}

type lowercase = ch | 'a' <= ch <= 'z' witness 'd'

method MultipleDimensions() {}

method DiagMatrix<A>(rows: int, cols: int, zero: A, one: A)
    returns (a: array2<A>)
    requires rows >= 0 && cols >= 0
{}

method PrintMatrix<A>(m: array2<A>) {}

////////TESTS////////

method TestLinearSearch1() {
  var a := new int[4] [5, 3, 8, 3];
  var n := LinearSearch(a, 3);
  assert n == 1;
}

method TestLinearSearch2() {
  var a := new int[3] [1, 2, 4];
  var n := LinearSearch(a, 7);
  assert n == 3;
}
