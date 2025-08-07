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

////////TESTS////////

method testMax1() {
  var numbers := [1, 5, 3, 9, 2];
  var result := max(numbers);
  assert result == 9;
}

method testMax2() {
  var numbers := [7];
  var result := max(numbers);
  assert result == 7;
}

method testMax3() {
  var numbers := [-5, -1, -10, -3];
  var result := max(numbers);
  assert result == -1;
}

method testRolling_max1() {
  var numbers := [1, 3, 2, 5, 4];
  var result := rolling_max(numbers);
  assert result == [1, 3, 3, 5, 5];
}

method testRolling_max2() {
  var numbers := [7, 2, 9, 1];
  var result := rolling_max(numbers);
  assert result == [7, 7, 9, 9];
}

method testRolling_max3() {
  var numbers := [10];
  var result := rolling_max(numbers);
  assert result == [10];
}
