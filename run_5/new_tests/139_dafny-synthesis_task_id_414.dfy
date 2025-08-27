method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
{}

////////TESTS////////

method TestAnyValueExists1() {
  var seq1 := [1, 2, 3];
  var seq2 := [2, 4, 6];
  var result := AnyValueExists(seq1, seq2);
  assert result == true;
}

method TestAnyValueExists2() {
  var seq1 := [1, 3, 5];
  var seq2 := [2, 4, 6];
  var result := AnyValueExists(seq1, seq2);
  assert result == false;
}
