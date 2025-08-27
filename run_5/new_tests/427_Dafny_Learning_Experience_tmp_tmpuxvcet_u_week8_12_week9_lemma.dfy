method AssignmentsToMark(students:int, tutors: int) returns (r:int)
    requires students > 0 && tutors > 1
    ensures r < students
{}

lemma DivisionLemma(n:int,d:int) 
    requires n > 0 && d>1
    ensures n/d < n


method AssignmentsToMarkOne(students:int, tutors: int) returns (r:int)
    requires students > 0 && tutors > 1
    ensures r < students
{}

lemma CommonElement(a:array<nat>, b:array<nat>)
    requires a.Length> 0 && b.Length > 0 && a[0] == b[0]
    ensures multiset(a[..])  * multiset(b[..]) == multiset([a[0]]) + multiset(a[1..]) * multiset(b[1..])
{}

////////TESTS////////

method TestAssignmentsToMark1() {
  var r := AssignmentsToMark(5, 3);
  assert r < 5;
}

method TestAssignmentsToMark2() {
  var r := AssignmentsToMark(10, 2);
  assert r < 10;
}

method TestAssignmentsToMarkOne1() {
  var r := AssignmentsToMarkOne(8, 4);
  assert r < 8;
}

method TestAssignmentsToMarkOne2() {
  var r := AssignmentsToMarkOne(15, 5);
  assert r < 15;
}
