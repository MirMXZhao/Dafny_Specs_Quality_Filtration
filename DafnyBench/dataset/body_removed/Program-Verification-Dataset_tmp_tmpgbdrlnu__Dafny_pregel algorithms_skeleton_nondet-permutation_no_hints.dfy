module Permutation
{
	/**
	 * Given n >= 0, generate a permuation of {0,...,n-1} nondeterministically.
	 */
	method Generate(n: int) returns (perm: array<int>)
		requires n >= 0
		ensures perm != null
		ensures perm.Length == n
		ensures fresh(perm)
		ensures isValid(perm, n)
	{}

	predicate isValid(a: array<int>, n: nat)
		requires a != null && a.Length == n
		reads a
	{}

	predicate distinct(a: array<int>)
		requires a != null
		reads a
	{}

	predicate distinct'(a: array<int>, n: int)
		requires a != null
		requires a.Length >= n
		reads a
	{}

	lemma CardinalityLemma (size: int, s: set<int>)
		requires size >= 0
		requires s == set x | 0 <= x < size
		ensures	size == |s|
	{}

	lemma CardinalityOrderingLemma<T> (s1: set<T>, s2: set<T>)
		requires s1 < s2
		ensures |s1| < |s2|
	{}

	lemma SetDiffLemma<T> (s1: set<T>, s2: set<T>)
		requires s1 < s2
		ensures s2 - s1 != {}
	{}
}
