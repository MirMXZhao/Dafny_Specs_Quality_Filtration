// RUN: %testDafnyForEachResolver "%s"


// Rustan Leino, June 2012.
// This file verifies an algorithm, due to Boyer and Moore, that finds the majority choice
// among a sequence of votes, see http://www.cs.utexas.edu/~moore/best-ideas/mjrty/.
// Actually, this algorithm is a slight variation on theirs, but the general idea for why
// it is correct is the same.  In the Boyer and Moore algorithm, the loop counter is advanced
// by exactly 1 each iteration, which means that there may or may not be a "current leader".
// In my program below, I had instead written the loop invariant to say there is always a
// "current leader", which requires the loop index sometimes to skip a value.
//
// This file has two versions of the algorithm.  In the first version, the given sequence
// of votes is assumed to have a (strict) majority choice, meaning that strictly more than
// 50% of the votes are for one candidate.  It is convenient to have a name for the majority
// choice, in order to talk about it in specifications.  The easiest way to do this in
// Dafny is probably to introduce a ghost parameter with the given properties.  That's what
// the algorithm does, see parameter K.  The postcondition is thus to output the value of
// K, which is done in the non-ghost out-parameter k.
// The proof of the algorithm requires two lemmas.  These lemmas are proved automatically
// by Dafny's induction tactic.
//
// In the second version of the program, the main method does not assume there is a majority
// choice.  Rather, it eseentially uses the first algorithm and then checks if what it
// returns really is a majority choice.  To do this, the specification of the first algorithm
// needs to be changed slightly to accommodate the possibility that there is no majority
// choice.  That change in specification is also reflected in the loop invariant.  Moreover,
// the algorithm itself now needs to extra 'if' statements to see if the entire sequence
// has been searched through.  (This extra 'if' is essentially already handled by Boyer and
// Moore's algorithm, because it increments the loop index by 1 each iteration and therefore
// already has a special case for the case of running out of sequence elements without a
// current leader.)
// The calling harness, DetermineElection, somewhat existentially comes up with the majority
// choice, if there is such a choice, and then passes in that choice as the ghost parameter K
// to the main algorithm.  Neat, huh?

// Language comment:
// The "(==)" that sits after some type parameters in this program says that the actual
// type argument must support equality.

// Advanced remark:
// There is a subtle situation in the verification of DetermineElection.  Suppose the type
// parameter Candidate denotes some type whose instances depend on which object are
// allocated.  For example, if Candidate is some class type, then more candidates can come
// into being by object allocations (using "new").  What does the quantification of
// candidates "c" in the postcondition of DetermineElection now mean--all candidates that
// existed in the pre-state or (the possibly larger set of) all candidates that exist in the
// post-state?  (It means the latter.)  And if there does not exist a candidate in majority
// in the pre-state, could there be a (newly created) candidate in majority in the post-state?
// This will require some proof.  The simplest argument seems to be that even if more candidates
// are created during the course of DetermineElection, such candidates cannot possibly
// be in majority in the sequence "a", since "a" can only contain candidates that were already
// created in the pre-state.  This property is easily specified by adding a postcondition
// to the Count function.  Alternatively, one could have added the antecedent "c in a" or
// "old(allocated(c))" to the "forall c" quantification in the postcondition of DetermineElection.

// About reading the proofs:
// Dafny proves the FindWinner algorithm from the given loop invariants and the two lemmas
// Lemma_Unique and Lemma_Split.  In showing this proof to some colleagues, they found they
// were not as quick as Dafny in constructing the proof from these ingredients.  For a human
// to understand the situation better, it helps to take smaller (and more) steps in the proof.
// At the end of this file, Nadia Polikarpova has written two versions of FindWinner that does
// that, using Dafny's support for calculational proofs.

function Count<T(==)>(a: seq<T>, s: int, t: int, x: T): int
  requires 0 <= s <= t <= |a|
{}

ghost predicate HasMajority<T>(a: seq<T>, s: int, t: int, x: T)
  requires 0 <= s <= t <= |a|
{}

// Here is the first version of the algorithm, the one that assumes there is a majority choice.

method FindWinner<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K) // K has a (strict) majority of the votes
  ensures k == K  // find K
{}

// ------------------------------------------------------------------------------

// Here is the second version of the program, the one that also computes whether or not
// there is a majority choice.

datatype Result<Candidate> = NoWinner | Winner(cand: Candidate)

method DetermineElection<Candidate(==,0,!new)>(a: seq<Candidate>) returns (result: Result<Candidate>)
  ensures result.Winner? ==> 2 * Count(a, 0, |a|, result.cand) > |a|
  ensures result.NoWinner? ==> forall c :: 2 * Count(a, 0, |a|, c) <= |a|
{}

// The difference between SearchForWinner for FindWinner above are the occurrences of the
// antecedent "hasWinner ==>" and the two checks for no-more-votes that may result in a "return"
// statement.

method SearchForWinner<Candidate(==)>(a: seq<Candidate>, ghost hasWinner: bool, ghost K: Candidate) returns (k: Candidate)
  requires |a| != 0
  requires hasWinner ==> 2 * Count(a, 0, |a|, K) > |a|  // K has a (strict) majority of the votes
  ensures hasWinner ==> k == K  // find K
{}

// ------------------------------------------------------------------------------

// Here are two lemmas about Count that are used in the methods above.

lemma Lemma_Split<T>(a: seq<T>, s: int, t: int, u: int, x: T)
  requires 0 <= s <= t <= u <= |a|
  ensures Count(a, s, t, x) + Count(a, t, u, x) == Count(a, s, u, x)
{}

lemma Lemma_Unique<T>(a: seq<T>, s: int, t: int, x: T, y: T)
  requires 0 <= s <= t <= |a|
  ensures x != y ==> Count(a, s, t, x) + Count(a, s, t, y) <= t - s
{}

// ------------------------------------------------------------------------------

// This version uses more calculations with integer formulas
method FindWinner'<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K) // K has a (strict) majority of the votes
  ensures k == K  // find K
{}

// This version uses more calculations with boolean formulas
method FindWinner''<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K)  // K has a (strict) majority of the votes
  ensures k == K  // find K
{}



method TestCount1() {
  var a := [1, 2, 1, 3, 1];
  var result := Count(a, 0, 5, 1);
  assert result == 3;
}

method TestCount2() {
  var a := [1, 2, 3, 4];
  var result := Count(a, 1, 3, 2);
  assert result == 1;
}

method TestHasMajority1() {
  var a := [1, 1, 1, 2, 2];
  var result := HasMajority(a, 0, 5, 1);
  assert result == true;
}

method TestHasMajority2() {
  var a := [1, 2, 3, 4];
  var result := HasMajority(a, 0, 4, 1);
  assert result == false;
}

method TestFindWinner1() {
  var a := [1, 1, 1, 2, 2];
  var k := FindWinner(a, 1);
  assert k == 1;
}

method TestFindWinner2() {
  var a := [3, 3, 3, 3, 1, 2];
  var k := FindWinner(a, 3);
  assert k == 3;
}

method TestDetermineElection1() {
  var a := [1, 1, 1, 2, 2];
  var result := DetermineElection(a);
  assert result.Winner? && result.cand == 1;
}

method TestDetermineElection2() {
  var a := [1, 2, 3, 4];
  var result := DetermineElection(a);
  assert result.NoWinner?;
}

method TestSearchForWinner1() {
  var a := [1, 1, 1, 2, 2];
  var k := SearchForWinner(a, true, 1);
  assert k == 1;
}

method TestSearchForWinner2() {
  var a := [1, 2, 3];
  var k := SearchForWinner(a, false, 1);
  assert k == 1;
}

method TestLemmaSplit1() {
  var a := [1, 2, 3, 4, 5];
  Lemma_Split(a, 0, 2, 4, 1);
}

method TestLemmaSplit2() {
  var a := [1, 1, 2, 2, 1];
  Lemma_Split(a, 1, 3, 5, 2);
}

method TestLemmaUnique1() {
  var a := [1, 2, 1, 3, 2];
  Lemma_Unique(a, 0, 5, 1, 2);
}

method TestLemmaUnique2() {
  var a := [1, 1, 1];
  Lemma_Unique(a, 0, 3, 1, 2);
}

method TestFindWinnerPrime1() {
  var a := [1, 1, 1, 2, 2];
  var k := FindWinner'(a, 1);
  assert k == 1;
}

method TestFindWinnerPrime2() {
  var a := [3, 3, 3, 3, 1];
  var k := FindWinner'(a, 3);
  assert k == 3;
}

method TestFindWinnerDoublePrime1() {
  var a := [1, 1, 1, 2, 2];
  var k := FindWinner''(a, 1);
  assert k == 1;
}

method TestFindWinnerDoublePrime2() {
  var a := [2, 2, 2, 2, 1, 3];
  var k := FindWinner''(a, 2);
  assert k == 2;
}
