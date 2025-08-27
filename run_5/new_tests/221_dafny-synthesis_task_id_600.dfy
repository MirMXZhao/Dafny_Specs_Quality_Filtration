method IsEven(n: int) returns (result: bool)
    ensures result <==> n % 2 == 0
{}

////////TESTS////////

method TestIsEven1() {
  var result := IsEven(4);
  assert result == true;
}

method TestIsEven2() {
  var result := IsEven(7);
  assert result == false;
}
