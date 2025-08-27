method IsPerfectSquare(n: int) returns (result: bool)
    requires n >= 0
    ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
    ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
{}

////////TESTS////////

method TestIsPerfectSquare1() {
  var result := IsPerfectSquare(16);
  assert result == true;
}

method TestIsPerfectSquare2() {
  var result := IsPerfectSquare(15);
  assert result == false;
}
