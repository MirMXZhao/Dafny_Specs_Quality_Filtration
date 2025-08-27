function power(a: int, n: int): int
  requires 0 <= a && 0 <= n;
  decreases n;{}

method compute_power(a: int, n: int) returns (s: int)
  requires n >= 0 && a >= 0;
  ensures s == power(a,n);
{}