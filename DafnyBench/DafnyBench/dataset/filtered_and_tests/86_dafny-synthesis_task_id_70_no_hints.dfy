method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
{}

method TestAllSequencesEqualLength1() {
  var sequences := [[1, 2, 3], [4, 5, 6], [7, 8, 9]];
  var result := AllSequencesEqualLength(sequences);
  assert result == true;
}

method TestAllSequencesEqualLength2() {
  var sequences := [[1, 2], [3, 4, 5], [6]];
  var result := AllSequencesEqualLength(sequences);
  assert result == false;
}
