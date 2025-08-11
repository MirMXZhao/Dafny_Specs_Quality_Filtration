method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
{}

////////TESTS////////

method TestIsGreater1() {
  var a := new int[3] [2, 5, 1];
  var result := IsGreater(6, a);
  assert result == true;
}

method TestIsGreater2() {
  var a := new int[4] [3, 7, 2, 4];
  var result := IsGreater(5, a);
  assert result == false;
}
