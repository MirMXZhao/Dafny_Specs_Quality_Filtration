
///////////////////////////
// Lemma to prove Transitive
// Got A<B, B<C.
// Prove A<C
///////////////////////////
predicate IsSubset(A: set, B: set) // <=
{}
// lemma - משפט
// subsetIsTransitive - lemma name.
// (A: set, B: set, C: set) - parameters using in lemma.
// "A" - parameter name, ": set " - parameter type (set = group).
lemma subsetIsTransitive(A: set, B: set, C: set)
    // requires - הנתון/הדרישה של הטענה 
    // "Pre1" - label,require התוית של 
    // "IsSubset" - function name. "(A, B)" function parameters
    requires Pre1 : IsSubset(A, B)
    requires Pre2 : IsSubset(B, C)
    // ensures - ״מבטיח לי״- צריך להוכיח
    ensures IsSubset(A, C)
// Start of ensure - תחילת ההוכחה
{}
