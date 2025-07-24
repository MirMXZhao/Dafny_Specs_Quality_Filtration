function sumInts( n: int ): int
    requires n >= 0;
{}


method SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
{}

method Main()
{}


