lemma Q1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment(L: bool, R: bool)
	ensures (L <==> R) <==> (L ==> R) && (!L ==> !R)
{} 


lemma Q2_DistributivityOfSetUnionOverSetIntersection(A: set, B: set, C: set)
	ensures A+(B*C) == (A+B)*(A+C)

		{}







lemma Q3_SetUnionIsAssociative(A: iset, B: iset, C: iset)
	ensures (A + B) + C == A + (B + C)

	{}


	
lemma preparation_for_Q4_SetDifferenceIs_NOT_Associative()
	ensures !forall A: set<int>, B: set<int>, C: set<int> :: (A - B) - C == A - (B - C)
{}

lemma Q4_Evidence_That_SetDifferenceIs_NOT_Associative() returns (A: set<int>, B: set<int>, C: set<int>)
	ensures (A - B) - C != A - (B - C)
	{}

////////TESTS////////

method TestQ1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment1() {
    Q1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment(true, true);
}

method TestQ1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment2() {
    Q1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment(false, true);
}

method TestQ2_DistributivityOfSetUnionOverSetIntersection1() {
    var A := {1, 2};
    var B := {2, 3};
    var C := {3, 4};
    Q2_DistributivityOfSetUnionOverSetIntersection(A, B, C);
}

method TestQ2_DistributivityOfSetUnionOverSetIntersection2() {
    var A := {5};
    var B := {6, 7};
    var C := {7, 8};
    Q2_DistributivityOfSetUnionOverSetIntersection(A, B, C);
}

method TestQ3_SetUnionIsAssociative1() {
    var A := iset{1, 2};
    var B := iset{3, 4};
    var C := iset{5, 6};
    Q3_SetUnionIsAssociative(A, B, C);
}

method TestQ3_SetUnionIsAssociative2() {
    var A := iset{10};
    var B := iset{20, 30};
    var C := iset{40};
    Q3_SetUnionIsAssociative(A, B, C);
}

method TestPreparation_for_Q4_SetDifferenceIs_NOT_Associative1() {
    preparation_for_Q4_SetDifferenceIs_NOT_Associative();
}

method TestPreparation_for_Q4_SetDifferenceIs_NOT_Associative2() {
    preparation_for_Q4_SetDifferenceIs_NOT_Associative();
}

method TestQ4_Evidence_That_SetDifferenceIs_NOT_Associative1() {
    var A, B, C := Q4_Evidence_That_SetDifferenceIs_NOT_Associative();
    assert (A - B) - C != A - (B - C);
}

method TestQ4_Evidence_That_SetDifferenceIs_NOT_Associative2() {
    var A, B, C := Q4_Evidence_That_SetDifferenceIs_NOT_Associative();
    assert (A - B) - C != A - (B - C);
}
