predicate IsSubset(A: set, B: set)
{
	forall n :: n in A ==> n in B
}

lemma subsetIsTransitive(A: set, B: set, C: set)
    requires Pre1 : IsSubset(A, B)
    requires Pre2 : IsSubset(B, C)
    ensures IsSubset(A, C)
{}