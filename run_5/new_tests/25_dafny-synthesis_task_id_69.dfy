method ContainsSequence(list: seq<seq<int>>, sub: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |list| && sub == list[i])
{}

////////TESTS////////

method TestContainsSequence1() {
  var list := [[1, 2, 3], [4, 5], [6, 7, 8, 9]];
  var sub := [4, 5];
  var result := ContainsSequence(list, sub);
  assert result == true;
}

method TestContainsSequence2() {
  var list := [[1, 2, 3], [4, 5], [6, 7, 8, 9]];
  var sub := [2, 3, 4];
  var result := ContainsSequence(list, sub);
  assert result == false;
}
