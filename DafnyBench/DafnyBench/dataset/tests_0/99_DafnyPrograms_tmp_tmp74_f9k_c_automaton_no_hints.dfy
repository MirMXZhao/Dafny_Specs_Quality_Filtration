class Automaton {

method ExecuteAutomaton(init: seq<bool>, rule: (bool, bool, bool) -> bool, steps: nat)
  returns (table: seq<seq<bool>>)
  requires |init| >= 2
  ensures |table| == 1 + steps
  ensures table[0] == init;
  ensures forall i | 0 <= i < |table| :: |table[i]| == |init|
  ensures forall i | 0 <= i < |table| - 1 ::
            forall j | 1 <= j <= |table[i]| - 2 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])
  ensures forall i | 0 <= i < |table| - 1 ::
            table[i + 1][0] == rule(false, table[i][0], table[i][1]) && table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
{}

function TheRule(a: bool, b: bool, c: bool) : bool
{
  a || b || c
}

function TheRule2(a: bool, b: bool, c: bool) : bool
{
  a && b && c
}

}

////////TESTS////////

method TestExecuteAutomaton1() {
  var automaton := new Automaton;
  var init := [true, false, true];
  var table := automaton.ExecuteAutomaton(init, automaton.TheRule, 2);
  assert table == [[true, false, true], [true, true, true], [true, true, true]];
}

method TestExecuteAutomaton2() {
  var automaton := new Automaton;
  var init := [false, false];
  var table := automaton.ExecuteAutomaton(init, automaton.TheRule2, 1);
  assert table == [[false, false], [false, false]];
}

method TestExecuteAutomaton3() {
  var automaton := new Automaton;
  var init := [true, true, false, false];
  var table := automaton.ExecuteAutomaton(init, automaton.TheRule2, 0);
  assert table == [[true, true, false, false]];
}

method TestTheRule1() {
  var automaton := new Automaton;
  var result := automaton.TheRule(false, false, false);
  assert result == false;
}

method TestTheRule2() {
  var automaton := new Automaton;
  var result := automaton.TheRule(true, false, true);
  assert result == true;
}

method TestTheRule21() {
  var automaton := new Automaton;
  var result := automaton.TheRule2(true, true, true);
  assert result == true;
}

method TestTheRule22() {
  var automaton := new Automaton;
  var result := automaton.TheRule2(true, false, true);
  assert result == false;
}
