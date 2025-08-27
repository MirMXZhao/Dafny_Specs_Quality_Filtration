method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
  requires threshold >= 0.0
  ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
  ensures !res ==> (forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==>  (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold)


{}

////////TESTS////////

method TestHasCloseElements1() {
  var numbers := [1.0, 2.0, 3.9, 4.0, 5.0, 2.2];
  var res := has_close_elements(numbers, 0.3);
  assert res == true;
}

method TestHasCloseElements2() {
  var numbers := [1.0, 2.0, 5.9, 4.0, 5.0];
  var res := has_close_elements(numbers, 0.8);
  assert res == false;
}
