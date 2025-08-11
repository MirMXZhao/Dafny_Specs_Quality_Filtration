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
{}

predicate is_permutation(a:seq<int>, b:seq<int>)
{}

predicate is_permutation2(a:seq<int>, b:seq<int>)
{}

method selection_sort(ns: array<int>) 
requires ns.Length >= 0
ensures is_sorted(ns[..])
ensures is_permutation2(old(ns[..]), ns[..])
modifies ns
{}

////////TESTS////////

method TestSelectionSort1() {
  var ns := new int[4];
  ns[0] := 3;
  ns[1] := 1;
  ns[2] := 4;
  ns[3] := 2;
  var old_content := ns[..];
  selection_sort(ns);
  assert is_sorted(ns[..]);
  assert is_permutation2(old_content, ns[..]);
}

method TestSelectionSort2() {
  var ns := new int[3];
  ns[0] := 5;
  ns[1] := 5;
  ns[2] := 5;
  var old_content := ns[..];
  selection_sort(ns);
  assert is_sorted(ns[..]);
  assert is_permutation2(old_content, ns[..]);
}
