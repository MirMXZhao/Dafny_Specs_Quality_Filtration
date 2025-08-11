module SetHelpers {

    lemma interSmallest<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures x * y == x
    {}

    lemma unionCardBound(x : set<nat>, y : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        requires forall e :: e in y ==> e < k
        ensures  forall e :: e in x + y ==> e < k
        ensures |x + y| <= k 
    {}

    lemma natSetCardBound(x : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        ensures |x| <= k 
    {}

    lemma {:induction k} successiveNatSetCardBound(x : set<nat>, k : nat) 
        requires x == set x: nat | 0 <= x < k :: x
        ensures |x| == k
    {}
    
    lemma cardIsMonotonic<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures |x| <= |y|
    {}

    lemma pigeonHolePrinciple<T>(x: set<T>, y : set<T>, z : set<T>)
        requires  x <= z 
        requires y <= z
        requires |x| >= 2 * |z| / 3 + 1
        requires |y| >= 2 * |z| / 3 + 1
        ensures |x * y| >= |z| / 3 + 1
    {} 

}

////////TESTS////////

method TestInterSmallest1() {
  var x := {1, 2};
  var y := {1, 2, 3, 4};
  SetHelpers.interSmallest(x, y);
}

method TestInterSmallest2() {
  var x := {};
  var y := {5, 10, 15};
  SetHelpers.interSmallest(x, y);
}

method TestUnionCardBound1() {
  var x := {0, 1, 2};
  var y := {2, 3, 4};
  var k := 5;
  SetHelpers.unionCardBound(x, y, k);
}

method TestUnionCardBound2() {
  var x := {0};
  var y := {1};
  var k := 3;
  SetHelpers.unionCardBound(x, y, k);
}

method TestNatSetCardBound1() {
  var x := {0, 1, 2};
  var k := 5;
  SetHelpers.natSetCardBound(x, k);
}

method TestNatSetCardBound2() {
  var x := {};
  var k := 10;
  SetHelpers.natSetCardBound(x, k);
}

method TestSuccessiveNatSetCardBound1() {
  var x := set x: nat | 0 <= x < 3 :: x;
  var k := 3;
  SetHelpers.successiveNatSetCardBound(x, k);
}

method TestSuccessiveNatSetCardBound2() {
  var x := set x: nat | 0 <= x < 0 :: x;
  var k := 0;
  SetHelpers.successiveNatSetCardBound(x, k);
}

method TestCardIsMonotonic1() {
  var x := {1, 2};
  var y := {1, 2, 3, 4};
  SetHelpers.cardIsMonotonic(
