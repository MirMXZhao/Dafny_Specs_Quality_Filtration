predicate sorted(a: seq<nat>)
{
    true // TODO
}

method Isort(a: array<nat>)
    modifies a
    ensures sorted(a[..])
{}