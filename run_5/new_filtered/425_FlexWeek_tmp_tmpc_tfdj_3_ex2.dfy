function abs(a:int):nat
{}

method aba(a:array<int>)returns (b:array<int>)
ensures a.Length == b.Length
ensures forall x :: 0<=x<b.Length ==> b[x] == abs(a[x])
{}