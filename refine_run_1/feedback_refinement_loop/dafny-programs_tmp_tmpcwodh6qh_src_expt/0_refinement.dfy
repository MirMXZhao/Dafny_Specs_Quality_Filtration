// Computes b raised to the power of n using recursive definition
// Returns b^n where b can be any integer and n must be non-negative
function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// Iteratively computes b raised to the power of n
// Uses a loop to calculate the exponentiation result
method computeExponent(b: int, n: nat) returns (res: int) 
  requires n >= 0
  ensures res == Expt(b, n)
{
  var i := 1;
  res := 1;
  while i < n + 1 
    invariant 0 < i <= n + 1
    invariant res == Expt(b, i - 1)
  {
    res := res * b;
    i := i + 1;
  }
}

// Proves the distributive law for exponentiation: x^a * x^b = x^(a+b)
// This lemma establishes that multiplying powers with the same base
// is equivalent to adding the exponents
// source: https://www.dcc.fc.up.pt/~nam/web/resources/vfs20/DafnyQuickReference.pdf
lemma {:induction a} exponentDistributiveLaw(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)
{
}