method IsArmstrong(n: int) returns (result: bool)
    requires 100 <= n < 1000
    ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
{}

////////TESTS////////

method TestIsArmstrong1() {
  var result := IsArmstrong(153);
  assert result == true;
}

method TestIsArmstrong2() {
  var result := IsArmstrong(123);
  assert result == false;
}
