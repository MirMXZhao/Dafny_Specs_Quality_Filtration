method ReplaceLastElement(first: seq<int>, second: seq<int>) returns (result: seq<int>)
    requires |first| > 0
    ensures |result| == |first| - 1 + |second|
    ensures forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i]
    ensures forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1]
{}

////////TESTS////////

method TestReplaceLastElement1() {
  var first := [1, 2, 3];
  var second := [4, 5];
  var result := ReplaceLastElement(first, second);
  assert result == [1, 2, 4, 5];
}

method TestReplaceLastElement2() {
  var first := [10];
  var second := [20, 30, 40];
  var result := ReplaceLastElement(first, second);
  assert result == [20, 30, 40];
}

method TestReplaceLastElement3() {
  var first := [7, 8];
  var second := [];
  var result := ReplaceLastElement(first, second);
  assert result == [7];
}
