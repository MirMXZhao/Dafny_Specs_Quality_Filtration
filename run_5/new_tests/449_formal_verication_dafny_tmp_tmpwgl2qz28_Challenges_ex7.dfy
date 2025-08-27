datatype Bases = A | C | G | T

method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{}

predicate below(first: Bases, second: Bases)
{
    first == second ||
    first == A || 
    (first == C && (second ==  G || second == T)) || 
    (first == G && second == T) ||
    second == T
}

predicate bordered(s:seq<Bases>)
{
    forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}

method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases);
{}

////////TESTS////////

method TestExchanger1() {
  var s := [A, C, G, T];
  var t := Exchanger(s, 1, 3);
  assert t == [A, T, G, C];
}

method TestExchanger2() {
  var s := [G, A, C];
  var t := Exchanger(s, 0, 2);
  assert t == [C, A, G];
}

method TestSorter1() {
  var bases := [T, A, G, C];
  var sobases := Sorter(bases);
  assert sobases == [A, C, G, T];
}

method TestSorter2() {
  var bases := [C, T, A];
  var sobases := Sorter(bases);
  assert sobases == [A, C, T];
}
