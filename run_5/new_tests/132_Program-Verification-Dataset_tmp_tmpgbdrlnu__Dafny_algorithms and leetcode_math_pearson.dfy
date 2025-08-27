function eight(x: nat):nat {
    9 * x + 5
}

predicate isOdd(x: nat) {
    x % 2 == 1
}

predicate isEven(x: nat) {
    x % 2 == 0
}

lemma eightL(x: nat)
    requires isOdd(x)
    ensures isEven(eight(x))
{

}

function nineteenf(x: nat): nat {
    7*x+4
}
function nineteens(x: nat): nat {
    3*x+11
}

lemma nineteenlemma(x: nat) 
    requires isEven(nineteenf(x))
    ensures isOdd(nineteens(x))
{

}

function relationDomain<T>(s: set<(T,T)>): set<T> {}

predicate reflexive<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    forall s :: s in S ==> (s,s) in R
}

predicate symmetric<T>(R: set<(T,T)>, S: set<T>)
    requires relationOnASet(R, S)
{
    forall x: T, y:T :: x in S && y in S && (x,y) in R ==> (y, x) in R
}

predicate transitive<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    forall a,b,c :: a in S && b in S && c in S && (a,b) in R && (b,c) in R ==> (a,c) in R
}

predicate equivalenceRelation<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    reflexive(R, S) && symmetric(R, S) && transitive(R, S)
}

predicate relationOnASet<T>(R: set<(T,T)>, S: set<T>) {
    forall ts :: ts in R ==> ts.0 in S && ts.1 in S
}

lemma reflexiveUnion<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
    requires |R_1| > 0
    requires |R_2| > 0
    requires |S_1| > 0
    requires |S_2| > 0
    requires relationOnASet(R_1, S_1)
    requires relationOnASet(R_2, S_2)
    requires reflexive(R_1, S_1)
    requires reflexive(R_2, S_2)
    ensures reflexive(R_1+R_2, S_1+S_2)
{

}

lemma symmetricUnion<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
    requires |R_1| > 0
    requires |R_2| > 0
    requires |S_1| > 0
    requires |S_2| > 0
    requires relationOnASet(R_1, S_1)
    requires relationOnASet(R_2, S_2)
    requires symmetric(R_1, S_1)
    requires symmetric(R_2, S_2)
    ensures symmetric(R_1+R_2, S_1+S_2)
{}

    
lemma transitiveUnion<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
    requires |R_1| > 0
    requires |R_2| > 0
    requires |S_1| > 0
    requires |S_2| > 0
    requires relationOnASet(R_1, S_1)
    requires relationOnASet(R_2, S_2)
    requires transitive(R_1, S_1)
    requires transitive(R_2, S_2)
    ensures transitive(R_1+R_2, S_1+S_2) 
{}

lemma transitiveUnionContra<T>()
  returns (
  R1: set<(T, T)>, S1: set<T>,
  R2: set<(T, T)>, S2: set<T>)
  ensures relationOnASet(R1, S1)
  ensures relationOnASet(R2, S2)
  ensures transitive(R1, S1)
  ensures transitive(R2, S2)
  ensures ! transitive(R1 + R2, S1 + S2)
{}

lemma notTrueAlways<T>()
  ensures !
  (forall S1 : set<T>, S2 : set<T>, R1 : set<(T,T)>, R2 : set<(T, T)> ::
  relationOnASet(R1, S1) &&
  relationOnASet(R2, S2) &&
  transitive(R1, S1) &&
  transitive(R2, S2)  ==> transitive(R1 + R2, S1 + S2)
  )
{}

////////TESTS////////

method testeight1() {
    var result := eight(3);
    assert result == 32;
}

method testeight2() {
    var result := eight(0);
    assert result == 5;
}

method testisOdd1() {
    var result := isOdd(7);
    assert result == true;
}

method testisOdd2() {
    var result := isOdd(4);
    assert result == false;
}

method testisEven1() {
    var result := isEven(6);
    assert result == true;
}

method testisEven2() {
    var result := isEven(5);
    assert result == false;
}

method testnineteenf1() {
    var result := nineteenf(2);
    assert result == 18;
}

method testnineteenf2() {
    var result := nineteenf(0);
    assert result == 4;
}

method testnineteens1() {
    var result := nineteens(3);
    assert result == 20;
}

method testnineteens2() {
    var result := nineteens(1);
    assert result == 14;
}

method testrelationDomain1() {
    var s := {(1, 2), (3, 4)};
    var result := relationDomain(s);
    assert result == {1, 2, 3, 4};
}

method testrelationDomain2() {
    var s := {(5, 5)};
    var result := relationDomain(s);
    assert result == {5};
}

method testreflexive1() {
    var R := {(1, 1), (2, 2)};
    var S := {1, 2};
    var result := reflexive(R, S);
    assert result == true;
}

method testreflexive2() {
    var R := {(1, 2)};
    var S := {1, 2};
    var result := reflexive(R, S);
    assert result == false;
}

method testsymmetric1() {
    var R := {(1, 2), (2, 1)};
    var S := {1, 2};
    var result := symmetric(R, S);
    assert result == true;
}

method testsymmetric2() {
    var R := {(1, 2)};
    var S := {1, 2};
    var result := symmetric(R, S);
    assert result == false;
}

method testtransitive1() {
    var R := {(1, 2), (2, 3), (1, 3)};
    var S := {1, 2, 3};
    var result := transitive(R, S);
    assert result == true;
}

method testtransitive2() {
    var R := {(1, 2), (2, 3)};
    var S := {1, 2, 3};
    var result := transitive(R, S);
    assert result == false;
}

method testequivalenceRelation1() {
    var R := {(1, 1), (2, 2), (1, 2), (2, 1)};
    var S := {1, 2};
    var result := equivalenceRelation(R, S);
    assert result == true;
}

method testequivalenceRelation2() {
    var R := {(1, 1), (2, 2)};
    var S := {1, 2};
    var result := equivalenceRelation(R, S);
    assert result == false;
}

method testrelationOnASet1() {
    var R := {(1, 2), (2, 3)};
    var S := {1, 2, 3};
    var result := relationOnASet(R, S);
    assert result == true;
}

method testrelationOnASet2() {
    var R := {(1, 4)};
    var S := {1, 2};
    var result := relationOnASet(R, S);
    assert result == false;
}

method testtransitiveUnionContra1() {
    var R1, S1, R2, S2 := transitiveUnionContra<int>();
    assert relationOnASet(R1, S1);
    assert relationOnASet(R2, S2);
    assert transitive(R1, S1);
    assert transitive(R2, S2);
    assert !transitive(R1 + R2, S1 + S2);
}

method testtransitiveUnionContra2() {
    var R1, S1, R2, S2 := transitiveUnionContra<string>();
    assert relationOnASet(R1, S1);
    assert relationOnASet(R2, S2);
    assert transitive(R1, S1);
    assert transitive(R2, S2);
    assert !transitive(R1 + R2, S1 + S2);
}
