function abs(x: int): int
{}

function max(a: int, b: int): int
{}

method Abs(x: int) returns (y: int)
    ensures abs(x) == y
{}

ghost function Double(val:int) : int
{
    2 * val
}

method TestDouble(val: int) returns (val2:int)
    ensures val2 == Double(val)
{}