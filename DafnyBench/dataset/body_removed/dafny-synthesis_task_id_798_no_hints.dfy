function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{}

method ArraySum(a: array<int>) returns (result: int)
    ensures result == sumTo(a, a.Length)
{}
