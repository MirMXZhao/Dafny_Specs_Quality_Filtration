method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (exists k :: 2 <= k < n && n % k == 0)
{}

////////TESTS////////

method TestIsNonPrime1() {
  var result := IsNonPrime(4);
  assert result == true;
}

method TestIsNonPrime2() {
  var result := IsNonPrime(7);
  assert result == false;
}
