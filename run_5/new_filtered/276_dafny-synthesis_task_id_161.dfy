predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method RemoveElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}