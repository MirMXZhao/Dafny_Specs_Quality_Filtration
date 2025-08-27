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