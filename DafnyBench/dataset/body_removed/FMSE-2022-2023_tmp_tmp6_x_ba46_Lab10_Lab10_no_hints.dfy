predicate IsOdd(x: int) {
    x % 2 == 1
}

newtype Odd = n : int | IsOdd(n) witness 3

trait OddListSpec
{
    var s: seq<Odd>
    var capacity: nat

    predicate Valid()
        reads this
    {}

    method insert(index: nat, element: Odd)
        modifies this
        requires 0 <= index <= |s|
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[index] == element
        ensures old(capacity) == capacity
        ensures Valid()

    method pushFront(element: Odd)
        modifies this
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[0] == element
        ensures old(capacity) == capacity
        ensures Valid()

    method pushBack(element: Odd)
        modifies this
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[|s| - 1] == element
        ensures old(capacity) == capacity
        ensures Valid()

    method remove(element: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        requires element in s
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method removeAtIndex(index: nat)
        modifies this
        requires Valid()
        requires |s| > 0
        requires 0 <= index < |s|
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method popFront() returns (x: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        ensures old(s)[0] == x
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method popBack() returns (x: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        ensures old(s)[|old(s)| - 1] == x
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method length() returns (n: nat)
        ensures n == |s|

    method at(index: nat) returns (x: Odd)
        requires 0 <= index < |s|

    method BinarySearch(element: Odd) returns (index: int)
        requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
        ensures 0 <= index ==> index < |s| && s[index] == element
        ensures index == -1 ==> element !in s[..]

    method mergedWith(l2: OddList) returns (l: OddList)
        requires Valid()
        requires l2.Valid()
        requires this.capacity >= 0 
        requires l2.capacity >= 0 
        requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
        requires forall i, j :: 0 <= i < j < |l2.s| ==> l2.s[i] <= l2.s[j]
        ensures l.capacity == this.capacity + l2.capacity
        ensures |l.s| == |s| + |l2.s|
}

class OddList extends OddListSpec
{
    constructor (capacity: nat)
        ensures Valid()
        ensures |s| == 0
        ensures this.capacity == capacity
    {}

    method insert(index: nat, element: Odd)
        modifies this
        requires 0 <= index <= |s|
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[index] == element
        ensures old(capacity) == capacity
        ensures Valid()
    {}

    method pushFront(element: Odd)
        modifies this
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[0] == element
        ensures old(capacity) == capacity
        ensures Valid()
    {}

    method pushBack(element: Odd)
        modifies this
        requires |s| + 1 <= this.capacity
        ensures |s| == |old(s)| + 1
        ensures s[|s| - 1] == element
        ensures old(capacity) == capacity
        ensures Valid()
    {}

    method remove(element: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        requires element in s
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()
    {}

    method removeAtIndex(index: nat)
        modifies this
        requires Valid()
        requires |s| > 0
        requires 0 <= index < |s|
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid()
    {}

    method popFront() returns (x: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        ensures old(s)[0] == x
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid() 
    {}

    method popBack() returns (x: Odd)
        modifies this
        requires Valid()
        requires |s| > 0
        ensures old(s)[|old(s)| - 1] == x
        ensures |s| == |old(s)| - 1
        ensures old(capacity) == capacity
        ensures Valid() 
    {}

    method length() returns (n: nat)
        ensures n == |s|
    {}

    method at(index: nat) returns (x: Odd)
    requires 0 <= index < |s|
        ensures s[index] == x
    {}

    method BinarySearch(element: Odd) returns (index: int)
        requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
        ensures 0 <= index ==> index < |s| && s[index] == element
        ensures index == -1 ==> element !in s[..]
    {}

    method mergedWith(l2: OddList) returns (l: OddList)
        requires Valid()
        requires l2.Valid()
        requires this.capacity >= 0 
        requires l2.capacity >= 0 
        requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
        requires forall i, j :: 0 <= i < j < |l2.s| ==> l2.s[i] <= l2.s[j]
        ensures l.capacity == this.capacity + l2.capacity
        ensures |l.s| == |s| + |l2.s|
    {}
}

trait CircularLinkedListSpec<T(==)>
{
    var l: seq<T>
    var capacity: nat 

    predicate Valid()
        reads this
    {}

    method insert(index: int, element: T)
    // allows for integer and out-of-bounds index due to circularity
    // managed by applying modulus
        modifies this
        requires |l| + 1 <= this.capacity
        ensures |old(l)| == 0 ==> l == [element]
        ensures |l| == |old(l)| + 1
        ensures |old(l)| > 0 ==> l[index % |old(l)|] == element
        ensures old(capacity) == capacity
        ensures Valid()

    method remove(element: T)
        modifies this
        requires Valid()
        requires |l| > 0
        requires element in l
        ensures |l| == |old(l)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method removeAtIndex(index: int)
        modifies this
        requires Valid()
        requires |l| > 0
        ensures |l| == |old(l)| - 1
        ensures old(capacity) == capacity
        ensures Valid()

    method length() returns (n: nat)
        ensures n == |l|

    method at(index: int) returns (x: T)
        requires |l| > 0
        ensures l[index % |l|] == x

    method nextAfter(index: int) returns (x: T)
        requires |l| > 0
        ensures |l| == 1 ==> x == l[0]
        ensures |l| > 1 && index % |l| == (|l| - 1) ==> x == l[0]
        ensures |l| > 1 && 0 <= index && |l| < (|l| - 1) ==> x == l[index % |l| + 1]
}

class CircularLinkedList<T(==)> extends CircularLinkedListSpec<T>
{
    constructor (capacity: nat)
        requires capacity >= 0
        ensures Valid()
        ensures |l| == 0
        ensures this.capacity == capacity
    {}

    method insert(index: int, element: T)
    // allows for integer and out-of-bounds index due to circularity
    // managed by applying modulus
        modifies this
        requires |l| + 1 <= this.capacity
        ensures |old(l)| == 0 ==> l == [element]
        ensures |l| == |old(l)| + 1
        ensures |old(l)| > 0 ==> l[index % |old(l)|] == element
        ensures old(capacity) == capacity
        ensures Valid()
    {}

    method remove(element: T)
        modifies this
        requires Valid()
        requires |l| > 0
        requires element in l
        ensures |l| == |old(l)| - 1
        ensures old(capacity) == capacity
        ensures Valid()
    {}

    method removeAtIndex(index: int)
        modifies this
        requires Valid()
        requires |l| > 0
        ensures |l| == |old(l)| - 1
        ensures old(capacity) == capacity
        ensures Valid()
    {}

    method length() returns (n: nat)
        ensures n == |l|
    {}

    method at(index: int) returns (x: T)
        requires |l| > 0
        ensures l[index % |l|] == x
    {}

    method nextAfter(index: int) returns (x: T)
        requires |l| > 0
        ensures |l| == 1 ==> x == l[0]
        ensures |l| > 1 && index % |l| == (|l| - 1) ==> x == l[0]
        ensures |l| > 1 && 0 <= index && |l| < (|l| - 1) ==> x == l[index % |l| + 1]
    {}

    method isIn(element: T) returns (b: bool)
        ensures |l| == 0 ==> b == false
        ensures |l| > 0 && b == true ==> exists i :: 0 <= i < |l| && l[i] == element
        ensures |l| > 0 && b == false ==> !exists i :: 0 <= i < |l| && l[i] == element
    {}
}
