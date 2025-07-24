method IsPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result <==> (forall k :: 2 <= k < n ==> n % k != 0)
{}

method TestIsPrime1() {
  var result := IsPrime(7);
  assert result == true;
}

method TestIsPrime2() {
  var result := IsPrime(12);
  assert result == false;
}
