function sum(a: array<int>, i: int): int
    requires 0 <= i < a.Length
    reads a
{}

method cumsum(a: array<int>, b: array<int>)
    requires  a.Length == b.Length && a.Length > 0 && a != b
    ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
    modifies b
{}