function abs(x: real): real
{}

method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
{}



method TestHasCloseElements1() {
  var numbers := [1.0, 2.0, 3.9, 4.0, 5.0, 2.2];
  var threshold := 0.3;
  var result := has_close_elements(numbers, threshold);
  assert result == true;
}

method TestHasCloseElements2() {
  var numbers := [1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
  var threshold := 0.5;
  var result := has_close_elements(numbers, threshold);
  assert result == false;
}
