method Triple (x: int) returns (r: int)
  ensures r == 3*x {}

method Caller() {}

method MinUnderSpec (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y {}

method Min (x: int, y: int) returns (r: int)
  ensures r <= x && r <= y
  ensures r == x || r == y {}

method MaxSum (x: int, y: int) returns (s:int, m: int)
  ensures s == x + y
  ensures x <= m && y <= m
  ensures m == x || m == y

method ReconstructFromMaxSum (s: int, m: int ) returns (x: int, y: int)
  requires s - m <= m
  ensures s == x + y
  ensures (m == y || m == x) && x <= m && y <= m
{}

function Average (a: int, b: int): int {
  (a + b) / 2
}

method Triple'(x: int) returns (r: int)
  ensures Average(2*r, 6*x) == 6*x
{}