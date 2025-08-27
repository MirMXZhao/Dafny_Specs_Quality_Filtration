method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
{}

////////TESTS////////

method TestContainsK1() {
  var s := [1, 2, 3, 4, 5];
  var result := ContainsK(s, 3);
  assert result == true;
}

method TestContainsK2() {
  var s := [1, 2, 4, 5];
  var result := ContainsK(s, 3);
  assert result == false;
}
