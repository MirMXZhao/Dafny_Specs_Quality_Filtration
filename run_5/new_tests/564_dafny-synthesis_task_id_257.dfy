method Swap(a: int, b: int) returns (result: seq<int>)
    ensures |result| == 2
    ensures result[0] == b
    ensures result[1] == a
{}

////////TESTS////////

method TestSwap1() {
  var result := Swap(5, 10);
  assert result == [10, 5];
}

method TestSwap2() {
  var result := Swap(-3, 7);
  assert result == [7, -3];
}
