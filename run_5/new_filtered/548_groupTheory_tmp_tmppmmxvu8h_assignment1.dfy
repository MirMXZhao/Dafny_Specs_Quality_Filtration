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