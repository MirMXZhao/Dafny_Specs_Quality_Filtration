method ReplaceLastElement(first: seq<int>, second: seq<int>) returns (result: seq<int>)
    requires |first| > 0
    ensures |result| == |first| - 1 + |second|
    ensures forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i]
    ensures forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1]
{}

method TestReplaceLastElement1() {
  var first := [1, 2, 3, 4];
  var second := [5, 6];
  var result := ReplaceLastElement(first, second);
  assert result == [1, 2, 3, 5, 6];
}

method TestReplaceLastElement2() {
  var first := [10];
  var second := [20, 30, 40];
  var result := ReplaceLastElement(first, second);
  assert result == [20, 30, 40];
}
