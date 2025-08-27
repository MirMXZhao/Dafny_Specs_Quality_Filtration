function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    decreases end;
    reads a;
    {}

method SumInRange(a: array<int>, start: int, end: int) returns (sum: int)
    requires a != null
    requires 0 <= start && start <= end && end <= a.Length
    ensures sum == sumTo(a, start, end)
    {}

////////TESTS////////

method TestSumInRange1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 2, 3, 4, 5;
  var sum := SumInRange(a, 1, 4);
  assert sum == 9;
}

method TestSumInRange2() {
  var a := new int[3];
  a[0], a[1], a[2] := 10, -5, 7;
  var sum := SumInRange(a, 0, 2);
  assert sum == 5;
}
