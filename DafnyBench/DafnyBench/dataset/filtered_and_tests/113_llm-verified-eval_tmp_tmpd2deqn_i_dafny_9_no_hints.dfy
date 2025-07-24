function isMax(m: int, numbers: seq<int>): bool
{}

method max(numbers: seq<int>) returns (result: int)
requires numbers != []
ensures isMax(result, numbers)
{}

method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{}



method TestRollingMax1() {
  var numbers := [1, 2, 3, 2, 3, 4, 2];
  var result := rolling_max(numbers);
  assert result == [1, 2, 3, 3, 3, 4, 4];
}

method TestRollingMax2() {
  var numbers := [5, 3, 4, 1, 2];
  var result := rolling_max(numbers);
  assert result == [5, 5, 5, 5, 5];
}
