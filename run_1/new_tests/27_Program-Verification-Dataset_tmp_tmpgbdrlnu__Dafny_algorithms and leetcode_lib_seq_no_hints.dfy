module Seq {
    export reveals *
    function ToSet<A>(xs: seq<A>): set<A>
        ensures forall x :: x in ToSet(xs) ==> x in xs
        ensures forall x :: x !in ToSet(xs) ==> x !in xs
    {}

    predicate substring1<A(==)>(sub: seq<A>, super: seq<A>) {}

    ghost predicate isSubstringAlt<A(!new)>(sub: seq<A>, super: seq<A>) {}

    predicate isSubstring<A(==)>(sub: seq<A>, super: seq<A>) {}

    lemma SliceOfSliceIsSlice<A>(xs: seq<A>, k: int, j: int, s: int, t: int)
        requires 0 <= k <= j <= |xs|
        requires 0 <= s <= t <= j-k
        ensures xs[k..j][s..t] == xs[(k+s)..(k+s+(t-s))]
    {}

    lemma AllSubstringsAreSubstrings<A>(subsub: seq<A>, sub: seq<A>, super: seq<A>)
        requires isSubstring(sub, super)
        requires isSubstring(subsub, sub)
        ensures isSubstring(subsub, super)
    {}

    predicate IsSuffix<T(==)>(xs: seq<T>, ys: seq<T>) {}
    
    predicate IsPrefix<T(==)>(xs: seq<T>, ys: seq<T>) {}

    lemma PrefixRest<T>(xs: seq<T>, ys: seq<T>)
        requires IsPrefix(xs, ys)
        ensures exists yss: seq<T> :: ys == xs + yss && |yss| == |ys|-|xs|;
    {
    }

    lemma IsSuffixReversed<T>(xs: seq<T>, ys: seq<T>)
        requires IsSuffix(xs, ys)
        ensures

////////TESTS////////

method TestToSet1() {
  var xs := [1, 2, 3, 2, 1];
  var result := ToSet(xs);
  assert result == {1, 2, 3};
}

method TestToSet2() {
  var xs := [5, 5, 5];
  var result := ToSet(xs);
  assert result == {5};
}
