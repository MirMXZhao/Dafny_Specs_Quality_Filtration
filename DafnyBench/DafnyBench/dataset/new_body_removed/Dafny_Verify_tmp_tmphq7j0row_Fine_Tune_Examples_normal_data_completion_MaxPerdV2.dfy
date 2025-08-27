function contains(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{}

function upper_bound(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{}

function is_max(m: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{}

method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
{}

