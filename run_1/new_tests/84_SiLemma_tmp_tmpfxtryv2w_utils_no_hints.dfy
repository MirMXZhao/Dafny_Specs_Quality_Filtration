module Utils {

    lemma AllBelowBoundSize(bound: nat)
        ensures
            var below := set n : nat | n < bound :: n;
            |below| ==  bound
    {}

    lemma SizeOfContainedSet(a: set<nat>, b: set<nat>)
        requires forall n: nat :: n in a ==> n in b
        ensures |a| <= |b|
    {}

    lemma BoundedSetSize(bound: nat, values: set<nat>)
        requires forall n :: n in values ==> n < bound
        ensures |values| <= bound
    {}

    lemma MappedSetSize<T, U>(s: set<T>, f: T->U, t: set<U>)
        requires forall n: T, m: T :: m != n ==> f(n) != f(m)
        requires t == set n | n in s :: f(n)
        ensures |s| == |t|
    {}

    lemma SetSizes<T>(a: set<T>, b: set<T>, c: set<T>)
        requires c == a + b
        requires forall t: T :: t in a ==> t !in b
        requires forall t: T :: t in b ==> t !in a
        ensures |c| == |a| + |b|
    {
    }

}

////////TESTS////////

method TestAllBelowBoundSize1() {
  var bound := 5;
  AllBelowBoundSize(bound);
  var below := set n : nat | n < bound :: n;
  assert |below| == 5;
}

method TestAllBelowBoundSize2() {
  var bound := 0;
  AllBelowBoundSize(bound);
  var below := set n : nat | n < bound :: n;
  assert |below| == 0;
}

method TestSizeOfContainedSet1() {
  var a := {1, 2, 3};
  var b := {0, 1, 2, 3, 4, 5};
  SizeOfContainedSet(a, b);
  assert |a| <= |b|;
}

method TestSizeOfContainedSet2() {
  var a := {10, 20};
  var b := {10, 15, 20, 25, 30};
  SizeOfContainedSet(a, b);
  assert |a| <= |b|;
}

method TestBoundedSetSize1() {
  var bound := 4;
  var values := {0, 1, 3};
  BoundedSetSize(bound, values);
  assert |values| <= bound;
}

method TestBoundedSetSize2() {
  var bound := 10;
  var values := {2, 5, 7, 9};
  BoundedSetSize(bound, values);
  assert |values| <= bound;
}

method TestMappedSetSize1() {
  var s := {1, 2, 3};
  var f := x => x * 2;
  var t := set n | n in s :: f(n);
  MappedSetSize(s, f, t);
  assert |s| == |t|;
}

method TestMappedSetSize2() {
  var s := {5, 10};
  var f := x => x + 1;
