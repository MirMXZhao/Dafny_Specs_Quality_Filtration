method M1(x: int, y: int) returns (r: int)
ensures r == x*y
decreases x < 0, x
{}

method A1(x: int, y: int) returns (r: int)
ensures r == x + y
{}
