function Average (a: int, b: int): int 
{}

method TripleConditions(x: int) returns (r: int) 
ensures r == 3 * x
{}

method Triple' (x: int) returns (r: int) 
    ensures Average(r, 3 * x) == 3 * x
    ensures r == 3 * x
{}

method ProveSpecificationsEquivalent(x: int) {}

