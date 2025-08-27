predicate IsSubset(A: set, B: set)
{
	forall n :: n in A ==> n in B
}

lemma subsetIsTransitive(A: set, B: set, C: set)
    requires Pre1 : IsSubset(A, B)
    requires Pre2 : IsSubset(B, C)
    ensures IsSubset(A, C)
{}

////////TESTS////////

method TestSubsetIsTransitive1() {
  var A := {1, 2};
  var B := {1, 2, 3};
  var C := {1, 2, 3, 4, 5};
  subsetIsTransitive(A, B, C);
}

method TestSubsetIsTransitive2() {
  var A := {};
  var B := {10};
  var C := {10, 20, 30};
  subsetIsTransitive(A, B, C);
}
