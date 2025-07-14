

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
{}

predicate symmetric<T>(R: set<(T,T)>, S: set<T>)
    requires relationOnASet(R, S)
{}

predicate transitive<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{}

predicate equivalenceRelation<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{}

predicate relationOnASet<T>(R: set<(T,T)>, S: set<T>) {}

// lemma equivUnion<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
//     requires |R_1| > 0
//     requires |R_2| > 0
//     requires |S_1| > 0
//     requires |S_2| > 0
//     requires relationOnASet(R_1, S_1)
//     requires relationOnASet(R_2, S_2)
//     requires equivalenceRelation(R_1, S_1)
//     requires equivalenceRelation(R_2, S_2)
//     ensures equivalenceRelation(R_1+R_2, S_1+S_2)
// {}

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

// lemma transitiveUnionContra<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
//     requires |R_1| > 0
//     requires |R_2| > 0
//     requires |S_1| > 0
//     requires |S_2| > 0
//     requires relationOnASet(R_1, S_1)
//     requires relationOnASet(R_2, S_2)
//     requires transitive(R_1, S_1)
//     requires transitive(R_2, S_2)
//     ensures exists (R_1+R_2, S_1+S_2) :: !transitive(R_1+R_2, S_1+S_2) 
// {}

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

method test() {}
