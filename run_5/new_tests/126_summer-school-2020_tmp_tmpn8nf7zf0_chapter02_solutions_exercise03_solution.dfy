predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

predicate SortSpec(input:seq<int>, output:seq<int>)
{
  && IsSorted(output)
  && multiset(output) == multiset(input)
}

method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
{}

method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures SortSpec(a+b, output)
{}

method fast_sort(input:seq<int>) returns (output:seq<int>)
{}

////////TESTS////////

method TestMergeSort1() {
  var input := [3, 1, 4, 1, 5];
  var output := merge_sort(input);
  assert output == [1, 1, 3, 4, 5];
}

method TestMergeSort2() {
  var input := [5, 2, 8, 1, 9];
  var output := merge_sort(input);
  assert output == [1, 2, 5, 8, 9];
}

method TestMerge1() {
  var a := [1, 3, 5];
  var b := [2, 4, 6];
  var output := merge(a, b);
  assert output == [1, 2, 3, 4, 5, 6];
}

method TestMerge2() {
  var a := [1, 2];
  var b := [3, 4, 5];
  var output := merge(a, b);
  assert output == [1, 2, 3, 4, 5];
}

method TestFastSort1() {
  var input := [3, 1, 4, 1, 5];
  var output := fast_sort(input);
  assert output == [1, 1, 3, 4, 5];
}

method TestFastSort2() {
  var input := [7, 2, 9, 1];
  var output := fast_sort(input);
  assert output == [1, 2, 7, 9];
}
