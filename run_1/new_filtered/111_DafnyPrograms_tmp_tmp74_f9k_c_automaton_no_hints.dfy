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