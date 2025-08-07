predicate strictSorted(s : seq<int>) {}


method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]
{}