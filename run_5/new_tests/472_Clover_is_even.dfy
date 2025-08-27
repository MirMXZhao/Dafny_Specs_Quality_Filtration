method ComputeIsEven(x:int) returns (is_even:bool)
  ensures (x % 2 == 0)==is_even
{}

////////TESTS////////

method TestComputeIsEven1() {
  var is_even := ComputeIsEven(4);
  assert is_even == true;
}

method TestComputeIsEven2() {
  var is_even := ComputeIsEven(7);
  assert is_even == false;
}
