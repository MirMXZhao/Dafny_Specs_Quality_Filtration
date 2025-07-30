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

////////TESTS////////

method testabs1() {
  var result := abs(5.0);
  assert result == 5.0;
}

method testabs2() {
  var result := abs(-3.0);
  assert result == 3.0;
}

method testabs3() {
  var result := abs(0.0);
  assert result == 0.0;
}

method testhas_close_elements1() {
  var numbers := [1.0, 2.0, 3.0, 4.0, 5.0];
  var threshold := 0.5;
  var result := has_close_elements(numbers, threshold);
  assert result == false;
}

method testhas_close_elements2() {
  var numbers := [1.0, 2.0, 3.1, 4.0, 5.0];
  var threshold := 1.5;
  var result := has_close_elements(numbers, threshold);
  assert result == true;
}

method testhas_close_elements3() {
  var numbers := [1.0];
  var threshold := 0.5;
  var result := has_close_elements(numbers, threshold);
  assert result == false;
}

method testhas_close_elements4() {
  var numbers: seq<real> := [];
  var threshold := 1.0;
  var result := has_close_elements(numbers, threshold);
  assert result == false;
}
