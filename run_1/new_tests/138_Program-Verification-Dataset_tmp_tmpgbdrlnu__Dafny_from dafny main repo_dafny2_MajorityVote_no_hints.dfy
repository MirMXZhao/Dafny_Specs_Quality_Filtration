function Count<T(==)>(a: seq<T>, s: int, t: int, x: T): int
  requires 0 <= s <= t <= |a|
{}

ghost predicate HasMajority<T>(a: seq<T>, s: int, t: int, x: T)
  requires 0 <= s <= t <= |a|
{}

method FindWinner<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K)
  ensures k == K
{}

datatype Result<Candidate> = NoWinner | Winner(cand: Candidate)

method DetermineElection<Candidate(==,0,!new)>(a: seq<Candidate>) returns (result: Result<Candidate>)
  ensures result.Winner? ==> 2 * Count(a, 0, |a|, result.cand) > |a|
  ensures result.NoWinner? ==> forall c :: 2 * Count(a, 0, |a|, c) <= |a|
{}

method SearchForWinner<Candidate(==)>(a: seq<Candidate>, ghost hasWinner: bool, ghost K: Candidate) returns (k: Candidate)
  requires |a| != 0
  requires hasWinner ==> 2 * Count(a, 0, |a|, K) > |a|
  ensures hasWinner ==> k == K
{}

lemma Lemma_Split<T>(a: seq<T>, s: int, t: int, u: int, x: T)
  requires 0 <= s <= t <= u <= |a|
  ensures Count(a, s, t, x) + Count(a, t, u, x) == Count(a, s, u, x)
{}

lemma Lemma_Unique<T>(a: seq<T>, s: int, t: int, x: T, y: T)
  requires 0 <= s <= t <= |a|

////////TESTS////////

method TestCount1() {
  var a := [1, 2, 1, 3, 1];
  var result := Count(a, 0, 5, 1);
  assert result == 3;
}

method TestCount2() {
  var a := ["apple", "banana", "apple", "cherry"];
  var result := Count(a, 1, 3, "apple");
  assert result == 1;
}

method TestFindWinner1() {
  var a := [1, 1, 2, 1, 1];
  var result := FindWinner(a, 1);
  assert result == 1;
}

method TestFindWinner2() {
  var a := ["Alice", "Bob", "Alice", "Alice", "Charlie", "Alice"];
  var result := FindWinner(a, "Alice");
  assert result == "Alice";
}

method TestDetermineElection1() {
  var a := [1, 1, 2, 1, 1];
  var result := DetermineElection(a);
  assert result == Winner(1);
}

method TestDetermineElection2() {
  var a := [1, 2, 3, 4];
  var result := DetermineElection(a);
  assert result == NoWinner;
}

method TestSearchForWinner1() {
  var a := [5, 5, 3, 5, 5];
  var result := SearchForWinner(a, true, 5);
  assert result == 5;
}

method TestSearchForWinner2() {
  var a := [1, 2, 3];
  var result := SearchForWinner(a, false, 1);
  assert result == 1;
}
