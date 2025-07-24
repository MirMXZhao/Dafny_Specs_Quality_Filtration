module Rope {
class Rope {
ghost var Contents: string;
ghost var Repr: set<Rope>;

var data: string;
var weight: nat;
var left: Rope?;
var right: Rope?;

ghost predicate Valid() 
    reads this, Repr
    ensures Valid() ==> this in Repr
{}

lemma contentSizeGtZero()
    requires Valid()
    ensures |Contents| > 0
{}

function getWeightsOfAllRightChildren(): nat
    reads right, Repr
    requires Valid()
    ensures right != null
        ==> getWeightsOfAllRightChildren() == |right.Contents|
{} 

function length(): nat
    reads Repr
    requires Valid()
    ensures |Contents| == length()
{}

// constructor for creating a terminal node
constructor Terminal(x: string)
    requires x != ""
    ensures Valid() && fresh(Repr)
        && left == null && right == null
        && data == x
{}   

predicate isTerminal()
    reads this, this.left, this.right
{}

method report(i: nat, j: nat) returns (s: string)
    requires 0 <= i <= j <= |this.Contents|
    requires Valid()
    ensures s == this.Contents[i..j]
{}

method toString() returns (s: string)
    requires Valid()
    ensures s == Contents
{}

method getCharAtIndex(index: nat) returns (c: char)
    requires Valid() && 0 <= index < |Contents|
    ensures c == Contents[index]
{}

static method concat(n1: Rope?, n2: Rope?) returns (n: Rope?) 
    requires (n1 != null) ==> n1.Valid()
    requires (n2 != null) ==> n2.Valid()
    requires (n1 != null && n2 != null) ==> (n1.Repr !! n2.Repr)

    ensures (n1 != null || n2 != null) <==> n != null && n.Valid()
    ensures (n1 == null && n2 == null) <==> n == null
    ensures (n1 == null && n2 != null)
        ==> n == n2 && n != null && n.Valid() && n.Contents == n2.Contents
    ensures (n1 != null && n2 == null)
        ==> n == n1 && n != null && n.Valid() && n.Contents == n1.Contents
    ensures (n1 != null && n2 != null)
        ==> n != null && n.Valid()
            && n.left == n1 && n.right == n2
            && n.Contents == n1.Contents + n2.Contents
            && fresh(n.Repr - n1.Repr - n2.Repr)
{} 


/**
    Dafny needs help to guess that in our definition, every rope must
    have non-empty Contents, otherwise it is represented by [null].

    The lemma contentSizeGtZero(n) is thus important to prove the
    postcondition of this method, in the two places where the lemma is
    invoked.
*/
static method split(n: Rope, index: nat) returns (n1: Rope?, n2: Rope?) 
    requires n.Valid() && 0 <= index <= |n.Contents|
    ensures index == 0
        ==> n1 == null && n2 != null && n2.Valid()
            && n2.Contents == n.Contents && fresh(n2.Repr - n.Repr)
    ensures index == |n.Contents|
        ==> n2 == null && n1 != null && n1.Valid()
            && n1.Contents == n.Contents && fresh(n1.Repr - n.Repr)
    ensures 0 < index < |n.Contents|
        ==> n1 != null && n1.Valid() && n2 != null && n2.Valid()
            && n1.Contents == n.Contents[..index]
            && n2.Contents == n.Contents[index..]
            && n1.Repr !! n2.Repr
            && fresh(n1.Repr - n.Repr) && fresh(n2.Repr - n.Repr)
{}

static method insert(n1: Rope, n2: Rope, index: nat) returns (n: Rope)
    requires n1.Valid() && n2.Valid() && n1.Repr !! n2.Repr
    requires 0 <= index < |n1.Contents|
    ensures n.Valid()
        && n.Contents ==
            n1.Contents[..index] + n2.Contents + n1.Contents[index..]
        && fresh(n.Repr - n1.Repr - n2.Repr)
{}

static method delete(n: Rope, i: nat, j: nat) returns (m: Rope?)
    requires n.Valid()
    requires 0 <= i < j <= |n.Contents|
    ensures (i == 0 && j == |n.Contents|) <==> m == null
    ensures m != null ==>
        m.Valid() &&
        m.Contents == n.Contents[..i] + n.Contents[j..] &&
        fresh(m.Repr - n.Repr)
{}

static method substring(n: Rope, i: nat, j: nat) returns (m: Rope?)
    requires n.Valid()
    requires 0 <= i < j <= |n.Contents|
    ensures (i == j) <==> m == null
    ensures m != null ==>
        m.Valid() &&
        m.Contents == n.Contents[i..j] &&
        fresh(m.Repr - n.Repr)
{}

}
// End of Rope Class
}
// End of Rope Module
