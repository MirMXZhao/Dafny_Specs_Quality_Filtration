/*
https://leetcode.com/problems/reverse-linked-list/description/
 * class ListNode {}

function reverseList(head: ListNode | null): ListNode | null {};
*/

datatype ListNode = Null | Node(val: nat, next: ListNode)

function reverse<A>(x: seq<A>): seq<A> 

{}

function nodeConcat(xs: ListNode, end: ListNode): ListNode {}

function reverseList(xs: ListNode): ListNode

{}

lemma ConcatNullIsRightIdentity(xs: ListNode) 
    ensures xs == nodeConcat(xs, Null)
{

}

lemma ConcatNullIsLeftIdentity(xs: ListNode) 
    ensures xs == nodeConcat(Null, xs)
{

}

lemma ConcatExtensionality(xs: ListNode)
    requires xs != Null
    ensures nodeConcat(Node(xs.val, Null), xs.next) == xs;
{

}

lemma ConcatAssociative(xs: ListNode, ys: ListNode, zs: ListNode)
    ensures nodeConcat(nodeConcat(xs, ys), zs) == nodeConcat(xs, nodeConcat(ys, zs))
{

}

lemma reverseSingleList(xs: ListNode) 
    requires xs != Null;
    requires xs.next == Null;
    ensures reverseList(xs) == xs;
{

}



lemma {:verify true} ConcatReverseList(xs:ListNode, ys: ListNode) 
    ensures reverseList(nodeConcat(xs,ys)) == nodeConcat(reverseList(ys), reverseList(xs))
{}

lemma reverseReverseListIsIdempotent(xs: ListNode)
    ensures reverseList(reverseList(xs)) == xs
{}

lemma {:induction false} reversePreservesMultiset<A>(xs: seq<A>) 
    ensures multiset(xs) == multiset(reverse(xs))
{}

lemma  reversePreservesLength<A>(xs: seq<A>)
    ensures |xs| == |reverse(xs)|
{

}

lemma  lastReverseIsFirst<A>(xs: seq<A>)
    requires |xs| > 0
    ensures xs[0] == reverse(xs)[|reverse(xs)|-1]
{}

lemma firstReverseIsLast<A>(xs: seq<A>)
    requires |xs| > 0
    ensures reverse(xs)[0] == xs[|xs|-1]
{

}

 lemma ReverseConcat<T>(xs: seq<T>, ys: seq<T>)
    ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
  {}


lemma reverseRest<A>(xs: seq<A>)
    requires |xs| > 0
    ensures reverse(xs) == [xs[ |xs| -1 ] ] + reverse(xs[0..|xs|-1])
{}


lemma SeqEq<T>(xs: seq<T>, ys: seq<T>)
    requires |xs| == |ys|
    requires forall i :: 0 <= i < |xs| ==> xs[i] == ys[i]
    ensures xs == ys
{
}

lemma ReverseIndexAll<T>(xs: seq<T>)
    ensures |reverse(xs)| == |xs|
    ensures forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1]
{}

  lemma ReverseIndex<T>(xs: seq<T>, i: int)
    requires 0 <= i < |xs|
    ensures |reverse(xs)| == |xs|
    ensures reverse(xs)[i] == xs[|xs| - i - 1]
  {}

lemma ReverseSingle<A>(xs: seq<A>) 
    requires |xs| == 1
    ensures reverse(xs) == xs
{

}

lemma reverseReverseIdempotent<A>(xs: seq<A>) 
    ensures reverse(reverse(xs)) == xs
{}

// var x := xs[0];
// assert xs == [x] + xs[1..];
// reversePreservesLength(xs);
// assert |xs| == |reverse(xs)|;
// calc {}
// var y := xs[|xs|-1];
// calc{}
// assert xs == xs[0..|xs|-1] + [y];
// lastReverseIsFirst(xs);
// lastReverseIsFirst(reverse(xs));

// assert reverse(reverse(xs))[0] == x;

/*
/**
https://leetcode.com/problems/linked-list-cycle/description/
 * Definition for singly-linked list.
 * class ListNode {}
 */

function hasCycle(head: ListNode | null): boolean {};
*/

method test() {}
