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

////////TESTS////////

method TestAbs1() {
    var y := Abs(-5);
    assert y == 5;
}

method TestAbs2() {
    var y := Abs(3);
    assert y == 3;
}

method TestTestDouble1() {
    var val2 := TestDouble(4);
    assert val2 == 8;
}

method TestTestDouble2() {
    var val2 := TestDouble(-3);
    assert val2 == -6;
}
