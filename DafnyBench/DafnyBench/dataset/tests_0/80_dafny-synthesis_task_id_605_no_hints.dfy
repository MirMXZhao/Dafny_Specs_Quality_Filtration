method IsPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (forall k :: 2 <= k < n ==> n % k != 0)
{}

////////TESTS////////

method TestIsPrime1() {
  var result := IsPrime(7);
  assert result == true;
}

method TestIsPrime2() {
  var result := IsPrime(8);
  assert result == false;
}

method TestIsPrime3() {
  var result := IsPrime(2);
  assert result == true;
}
