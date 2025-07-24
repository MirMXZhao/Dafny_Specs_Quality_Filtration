predicate IsSorted(s:seq<int>)
{}

predicate SortSpec(input:seq<int>, output:seq<int>)
{}

//lemma SequenceConcat(s:seq<int>, pivot:int)
//  requires 0<=pivot<|s|
//  ensures s[..pivot] + s[pivot..] == s
//{
//}

method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures SortSpec(input, output)
{}

method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
//  ensures IsSorted(output)
  ensures SortSpec(a+b, output)
  //decreases |a|+|b|
{}

method fast_sort(input:seq<int>) returns (output:seq<int>)
//  ensures SortSpec(input, output)
{}

