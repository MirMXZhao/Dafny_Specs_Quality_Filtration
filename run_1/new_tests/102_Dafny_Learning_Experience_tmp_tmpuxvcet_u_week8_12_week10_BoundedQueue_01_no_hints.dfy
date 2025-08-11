class BoundedQueue<T(0)>
{
 ghost var contents: seq<T>
 ghost var N: nat
 ghost var Repr: set<object>
var data: array<T>
 var wr: nat
 var rd: nat
  
  ghost predicate Valid()
 reads this, Repr
ensures Valid() ==> this in Repr && |contents| <= N 
 {}

 constructor (N: nat)
ensures Valid() && fresh(Repr)
ensures contents == [] && this.N == N
{}
method Insert(x:T)
requires Valid()
requires |contents| != N
modifies Repr
ensures contents == old(contents) + [x]
ensures N == old(N)
ensures Valid() && fresh(Repr - old(Repr))
{}

method Remove() returns (x:T)
requires Valid()
requires |contents| != 0
modifies Repr
ensures contents == old(contents[1..]) && old(contents[0]) == x
ensures N == old(N)
ensures Valid() && fresh(Repr - old(Repr))
{}
}

////////TESTS////////

method TestBoundedQueue1() {
    var queue := new BoundedQueue<int>(3);
    queue.Insert(5);
    queue.Insert(10);
    var x := queue.Remove();
    assert x == 5;
}

method TestBoundedQueue2() {
    var queue := new BoundedQueue<int>(2);
    queue.Insert(7);
    queue.Insert(14);
    var y := queue.Remove();
    assert y == 7;
}
