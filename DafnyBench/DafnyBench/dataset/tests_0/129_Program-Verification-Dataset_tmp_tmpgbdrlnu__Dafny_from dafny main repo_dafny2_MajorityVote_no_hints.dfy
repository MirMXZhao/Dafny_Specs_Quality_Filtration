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

method TestCount1() {
  var a := [1, 2, 1, 3, 1];
  var result := Count(a, 0, 5, 1);
  assert result == 3;
}

method TestCount2() {
  var a := ['a', 'b', 'c', 'b'];
  var result := Count(a, 1, 3, 'b');
  assert result == 1;
}

method TestCount3() {
  var a := [5, 5, 5];
  var result := Count(a, 0, 0, 5);
  assert result == 0;
}

method TestDetermineElection1() {
  var a := [1, 1, 1, 2, 2];
  var result := DetermineElection(a);
  assert result == Winner(1);
}

method TestDetermineElection2() {
  var a := [1, 2, 3, 4];
  var result := DetermineElection(a);
  assert result == NoWinner;
}

method TestDetermineElection3() {
  var a := [];
  var result := DetermineElection(a);
  assert result == NoWinner;
}

method TestSearchForWinner1() {
  var a := [5, 5, 5, 3, 3];
  var k := SearchForWinner(a, true, 5);
  assert k == 5;
}

method TestSearchForWinner2() {
  var a := [7, 8, 9];
  var k := SearchForWinner(a, false, 7);
  assert k == 7;
}

method TestSearchForWinner3() {
  var a := [1];
  var k := SearchForWinner(a, true, 1);
  assert k == 1;
}

method TestFindWinner1() {
  var a := [10, 10, 10, 20];
  var k := FindWinner(a, 10);
  assert k == 10;
}

method TestFindWinner2() {
  var a := ['x', 'x', 'y'];
  var k := FindWinner(a, 'x');
  assert k == 'x';
}

method TestFindWinner3() {
  var a := [99];
  var k := FindWinner(a, 99);
  assert k == 99;
}

method TestFindWinner'1() {
  var a := [42, 42, 42, 99, 99];
  var k := FindWinner'(a, 42);
  assert k == 42;
}

method TestFindWinner'2() {
  var a := [100];
  var k := FindWinner'(a, 100);
  assert k == 100;
}

method TestFindWinner'3() {
  var a := [3, 3, 3, 3, 4, 4, 4];
  var k := FindWinner'(a, 3);
  assert k == 3;
}

method TestFindWinner''1() {
  var a := [77, 88, 77, 77];
  var k := FindWinner''(a, 77);
  assert k == 77;
}

method TestFindWinner''2() {
  var a := [55, 55, 55, 55, 66];
  var k := FindWinner''(a, 55);
  assert k == 55;
}

method TestFindWinner''3() {
  var a := [2, 2, 1];
  var k := FindWinner''(a, 2);
  assert k == 2;
}
