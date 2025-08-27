method ContainsConsecutiveNumbers(a: array<int>) returns (result: bool)
    requires a.Length>0
    ensures result <==> (exists i :: 0 <= i < a.Length - 1 && a[i] + 1 == a[i + 1])
{}

////////TESTS////////

method TestContainsConsecutiveNumbers1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 1, 3, 4, 7;
  var result := ContainsConsecutiveNumbers(a);
  assert result == true;
}

method TestContainsConsecutiveNumbers2() {
  var a := new int[3];
  a[0], a[1], a[2] := 2, 4, 8;
  var result := ContainsConsecutiveNumbers(a);
  assert result == false;
}
