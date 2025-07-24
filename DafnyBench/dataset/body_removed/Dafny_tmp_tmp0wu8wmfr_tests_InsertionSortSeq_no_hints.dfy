// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

predicate IsSorted( s: seq<int> )
{}

method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
{}
