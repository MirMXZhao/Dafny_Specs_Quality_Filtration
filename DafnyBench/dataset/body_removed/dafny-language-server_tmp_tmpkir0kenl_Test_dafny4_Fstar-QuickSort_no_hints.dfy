// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A Dafny rendition of an F* version of QuickSort (included at the bottom of this file).
// Unlike the F* version, Dafny also proves termination and does not use any axioms.  However,
// Dafny needs help with a couple of lemmas in places where F* does not need them.
// Comments below show differences between the F* and Dafny versions.

datatype List<T> = Nil | Cons(T, List)

function length(list: List): nat  // for termination proof
{}

// In(x, list) returns the number of occurrences of x in list
function In(x: int, list: List<int>): nat
{}

predicate SortedRange(m: int, n: int, list: List<int>)
{}

function append(n0: int, n1: int, n2: int, n3: int, i: List<int>, j: List<int>): List<int>
  requires n0 <= n1 <= n2 <= n3
  requires SortedRange(n0, n1, i) && SortedRange(n2, n3, j)
  ensures SortedRange(n0, n3, append(n0, n1, n2, n3, i, j))
  ensures forall x :: In(x, append(n0, n1, n2, n3, i, j)) == In(x, i) + In(x, j)
{}

function partition(x: int, l: List<int>): (List<int>, List<int>)
  ensures var (lo, hi) := partition(x, l);
    (forall y :: In(y, lo) == if y <= x then In(y, l) else 0) &&
    (forall y :: In(y, hi) == if x < y then In(y, l) else 0) &&
    length(l) == length(lo) + length(hi)  // for termination proof
{}

function sort(min: int, max: int, i: List<int>): List<int>
  requires min <= max
  requires forall x :: In(x, i) != 0 ==> min <= x <= max
  ensures SortedRange(min, max, sort(min, max, i))
  ensures forall x :: In(x, i) == In(x, sort(min, max, i))
{}

/*
module Sort

type SortedRange : int => int => list int => E
assume Nil_Sorted : forall (n:int) (m:int). n <= m <==> SortedRange n m []
assume Cons_Sorted: forall (n:int) (m:int) (hd:int) (tl:list int).
               SortedRange hd m tl && (n <= hd) && (hd <= m)
          <==> SortedRange n m (hd::tl)

val append: n1:int -> n2:int{n1 <= n2} -> n3:int{n2 <= n3} -> n4:int{n3 <= n4}
         -> i:list int{SortedRange n1 n2 i}
         -> j:list int{SortedRange n3 n4 j}
         -> k:list int{}
let rec append n1 n2 n3 n4 i j = match i with
  | [] ->
    (match j with
      | [] -> j
      | _::_ -> j)
  | hd::tl -> hd::(append hd n2 n3 n4 tl j)

val partition: x:int
            -> l:list int
            -> (lo:list int
                * hi:list int{})
let rec partition x l = match l with
  | [] -> ([], [])
  | hd::tl ->
    let lo, hi = partition x tl in
    if hd <= x
    then (hd::lo, hi)
    else (lo, hd::hi)

val sort: min:int
       -> max:int{min <= max}
       -> i:list int {}
       -> j:list int{}
let rec sort min max i = match i with
  | [] -> []
  | hd::tl ->
    let lo,hi = partition hd tl in
    let i' = sort min hd lo in
    let j' = sort hd max hi in
    append min hd hd max i' (hd::j')

*/

