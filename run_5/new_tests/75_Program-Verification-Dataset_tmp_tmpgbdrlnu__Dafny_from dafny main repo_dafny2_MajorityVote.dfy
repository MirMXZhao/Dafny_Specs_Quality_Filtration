function Count<T(==)>(a: seq<T>, s: int, t: int, x: T): int
  requires 0 <= s <= t <= |a|
{}

ghost predicate HasMajority<T>(a: seq<T>, s: int, t: int, x: T)
  requires 0 <= s <= t <= |a|
{
  2 * Count(a, s, t, x) > t - s
}

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
  ensures x != y ==> Count(a, s, t, x) + Count(a, s, t, y) <= t - s
{}

method FindWinner'<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K)
  ensures k == K
{}

method FindWinner''<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K)
  ensures k == K
{}

////////TESTS////////

method TestFindWinner1() {
  var a := [1, 1, 2, 1, 1];
  ghost var K := 1;
  var k := FindWinner(a, K);
  assert k == 1;
}

method TestFindWinner2() {
  var a := [3, 3, 3, 2, 2];
  ghost var K := 3;
  var k := FindWinner(a, K);
  assert k == 3;
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
  var a := [1, 1, 2, 1, 1];
  ghost var hasWinner := true;
  ghost var K := 1;
  var k := SearchForWinner(a, hasWinner, K);
  assert k == 1;
}

method TestSearchForWinner2() {
  var a := [5, 5, 5];
  ghost var hasWinner := true;
  ghost var K := 5;
  var k := SearchForWinner(a, hasWinner, K);
  assert k == 5;
}

method TestFindWinner'1() {
  var a := [7, 7, 8, 7];
  ghost var K := 7;
  var k := FindWinner'(a, K);
  assert k == 7;
}

method TestFindWinner'2() {
  var a := [9, 9, 9, 9, 9, 6];
  ghost var K := 9;
  var k := FindWinner'(a, K);
  assert k == 9;
}

method TestFindWinner''1() {
  var a := [4, 4, 4, 2, 2];
  ghost var K := 4;
  var k := FindWinner''(a, K);
  assert k == 4;
}

method TestFindWinner''2() {
  var a := [10, 10, 10];
  ghost var K := 10;
  var k := FindWinner''(a, K);
  assert k == 10;
}
