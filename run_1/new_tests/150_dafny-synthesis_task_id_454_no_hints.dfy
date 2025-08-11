method ContainsZ(s: string) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
{}

////////TESTS////////

method TestContainsZ1() {
  var result := ContainsZ("hello world");
  assert result == false;
}

method TestContainsZ2() {
  var result := ContainsZ("amazing");
  assert result == true;
}
