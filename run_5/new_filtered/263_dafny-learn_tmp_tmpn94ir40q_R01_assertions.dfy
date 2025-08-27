method Abs(x: int) returns (y: int)
  ensures 0 <= y
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
{}

method Max(a: int, b: int) returns (c: int)
  ensures c >= a
  ensures c >= b
{}