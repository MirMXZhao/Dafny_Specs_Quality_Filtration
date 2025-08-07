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

method test_find_min_index1() {
  var a := new int[5] [3, 1, 4, 1, 5];
  var min_i := find_min_index(a, 0, 5);
  assert min_i == 1;
}

method test_find_min_index2() {
  var a := new int[4] [7, 2, 9, 2];
  var min_i := find_min_index(a, 1, 3);
  assert min_i == 1;
}

method test_find_min_index3() {
  var a := new int[3] [5, 5, 5];
  var min_i := find_min_index(a, 0, 3);
  assert min_i == 0;
}

method test_is_sorted1() {
  var s := [1, 2, 3, 4, 5];
  var result := is_sorted(s);
  assert result == true;
}

method test_is_sorted2() {
  var s := [5, 3, 1];
  var result := is_sorted(s);
  assert result == false;
}

method test_is_permutation1() {
  var a := [1, 2, 3];
  var b := [3, 1, 2];
  var result := is_permutation(a, b);
  assert result == true;
}

method test_is_permutation2() {
  var a := [1, 2, 3];
  var b := [1, 2, 4];
  var result := is_permutation(a, b);
  assert result == false;
}

method test_is_permutation2_1() {
  var a := [1, 2, 3];
  var b := [2, 3, 1];
  var result := is_permutation2(a, b);
  assert result == true;
}

method test_is_permutation2_2() {
  var a := [1, 1, 2];
  var b := [1, 2, 3];
  var result := is_permutation2(a, b);
  assert result == false;
}

method test_selection_sort1() {
  var ns := new int[4] [3, 1, 4, 2];
  selection_sort(ns);
  assert is_sorted(ns[..]);
  assert is_permutation2([3, 1, 4, 2], ns[..]);
}

method test_selection_sort2() {
  var ns := new int[3] [5, 5, 5];
  selection_sort(ns);
  assert is_sorted(ns[..]);
  assert is_permutation2([5, 5, 5], ns[..]);
}
