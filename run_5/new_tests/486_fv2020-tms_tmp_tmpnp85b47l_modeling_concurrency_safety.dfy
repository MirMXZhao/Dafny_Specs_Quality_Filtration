type Process(==) = int

datatype CState = Thinking | Hungry | Eating

class TicketSystem
{
  var ticket: int
  var serving: int

  const P: set<Process>

  var cs: map<Process, CState>
  var t: map<Process, int>

  predicate Valid()
    reads this
  {
    && cs.Keys == t.Keys == P
    && serving <= ticket
    && (forall p ::
      p in P && cs[p] != Thinking
      ==> serving <= t[p] < ticket
    )
    && (forall p, q ::
      p in P && q in P && p != q && cs[p] != Thinking && cs[q] != Thinking
      ==> t[p] != t[q]
    )
    && (forall p ::
      p in P && cs[p] == Eating
      ==> t[p] == serving
    )
  }

  constructor (processes: set<Process>)
    ensures Valid()
    ensures P == processes
  {}

  method Request(p: Process)
    requires Valid() && p in P && cs[p] == Thinking
    modifies this
    ensures Valid()
  {}

  method Enter(p: Process)
    requires Valid() && p in P && cs[p] == Hungry
    modifies this
    ensures Valid()
  {}

  method Leave(p: Process)
    requires Valid() && p in P && cs[p] == Eating
    modifies this
    ensures Valid()
  {}

  lemma MutualExclusion(p: Process, q: Process)
    requires Valid() && p in P && q in P
    requires cs[p] == Eating && cs[q] == Eating
    ensures p == q
  {

  }
}

method Run(processes: set<Process>)
  requires processes != {}
  decreases *
{}

method RunFromSchedule(processes: set<Process>, schedule: nat -> Process)
  requires processes != {}
  requires forall n :: schedule(n) in processes
  decreases *
{}

////////TESTS////////

method TestRun1() {
  var processes := {1, 2};
  Run(processes);
}

method TestRun2() {
  var processes := {5};
  Run(processes);
}

method TestRunFromSchedule1() {
  var processes := {1, 2};
  var schedule := (n: nat) => if n % 2 == 0 then 1 else 2;
  RunFromSchedule(processes, schedule);
}

method TestRunFromSchedule2() {
  var processes := {3, 4, 5};
  var schedule := (n: nat) => 3;
  RunFromSchedule(processes, schedule);
}
