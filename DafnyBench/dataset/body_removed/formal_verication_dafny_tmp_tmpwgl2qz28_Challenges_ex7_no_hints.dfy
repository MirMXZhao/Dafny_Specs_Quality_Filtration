// see pdf 'ex6 & 7 documentation' for excercise question

datatype Bases = A | C | G | T

//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{}

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
predicate below(first: Bases, second: Bases)
{}

//checks if a sequence is in base order
predicate bordered(s:seq<Bases>)
{}

method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases);
{}

method Testerexchange() {}

method Testsort() {}

