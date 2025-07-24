function countTo( a:array<bool>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{}

method CountTrue(a: array<bool>) returns (result: int)
    requires a != null
    ensures result == countTo(a, a.Length)
{}