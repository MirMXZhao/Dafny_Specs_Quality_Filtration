 class BoundedQueue<T(0)>
{
 // abstract state
 ghost var contents: seq<T> // the contents of the bounded queue
 ghost var N: nat // the (maximum) size of the bounded queue
 ghost var Repr: set<object>
 // concrete state
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


method TestBoundedQueueInsert() {
  var queue := new BoundedQueue<int>(3);
  queue.Insert(5);
  assert queue.contents == [5];
  assert queue.N == 3;
}

method TestBoundedQueueRemove() {
  var queue := new BoundedQueue<int>(2);
  queue.Insert(10);
  queue.Insert(20);
  var x := queue.Remove();
  assert x == 10;
  assert queue.contents == [20];
}
