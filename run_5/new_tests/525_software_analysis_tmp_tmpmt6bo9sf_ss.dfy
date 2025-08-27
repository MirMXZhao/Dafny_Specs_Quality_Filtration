method find_min_index(a : array<int>, s: int, e: int) returns (min_i: int)
requires a.Length > 0
requires 0 <= s < a.Length
requires e <= a.Length
requires e > s

ensures min_i >= s 
ensures min_i < e 
ensures forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{}

predicate is_sorted(ss: seq<int>)
{
    forall i, j: int:: 0 <= i <= j < |ss| ==> ss[i] <= ss[j]
}

predicate is_permutation(a:seq<int>, b:seq<int>)
decreases |a|
decreases |b|
{}

predicate is_permutation2(a:seq<int>, b:seq<int>)
{
    multiset(a) == multiset(b)
}

method selection_sort(ns: array<int>) 
requires ns.Length >= 0
ensures is_sorted(ns[..])
ensures is_permutation2(old(ns[..]), ns[..])
modifies ns
{}

////////TESTS////////

method TestSelectionSort1() {
  var arr := new int[4];
  arr[0], arr[1], arr[2], arr[3] := 64, 34, 25, 12;
  var original := arr[..];
  selection_sort(arr);
  assert is_sorted(arr[..]);
  assert is_permutation2(original, arr[..]);
}

method TestSelectionSort2() {
  var arr := new int[3];
  arr[0], arr[1], arr[2] := 5, 2, 8;
  var original := arr[..];
  selection_sort(arr);
  assert is_sorted(arr[..]);
  assert is_permutation2(original, arr[..]);
}
