ghost function pow(a: int, e: nat): int {}

method Pow(a: nat, n: nat) returns (y: nat)
ensures y == pow(a, n)
{}
