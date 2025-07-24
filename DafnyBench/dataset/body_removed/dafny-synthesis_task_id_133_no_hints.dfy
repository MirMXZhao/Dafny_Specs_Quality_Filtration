function sumNegativesTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{}

method SumOfNegatives(a: array<int>) returns (result: int)
    ensures result == sumNegativesTo(a, a.Length)
{}