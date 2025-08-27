function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{}

method sum_array( a: array<int>) returns (sum: int)
  requires a != null;
  ensures sum == sumTo(a, a.Length);
{}

