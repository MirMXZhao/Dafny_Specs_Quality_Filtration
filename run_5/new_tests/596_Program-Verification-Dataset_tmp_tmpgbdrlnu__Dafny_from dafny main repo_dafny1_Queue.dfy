class Queue<T(0)> {
  var head: Node<T>
  var tail: Node<T>

  ghost var contents: seq<T>
  ghost var footprint: set<object>
  ghost var spine: set<Node<T>>

  ghost predicate Valid()
    reads this, footprint
  {
    this in footprint && spine <= footprint &&
    head in spine &&
    tail in spine &&
    tail.next == null &&
    (forall n ::
      n in spine ==>
        n.footprint <= footprint && this !in n.footprint &&
        n.Valid() &&
        (n.next == null ==> n == tail)) &&
    (forall n ::
      n in spine ==>
        n.next != null ==> n.next in spine) &&
    contents == head.tailContents
  }

  constructor Init()
    ensures Valid() && fresh(footprint - {this})
    ensures |contents| == 0
  {}

  method Rotate()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents)[1..] + old(contents)[..1]
  {}

  method RotateAny()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures |contents| == |old(contents)|
    ensures exists i :: 0 <= i && i <= |contents| &&
              contents == old(contents)[i..] + old(contents)[..i]
  {}

  method IsEmpty() returns (isEmpty: bool)
    requires Valid()
    ensures isEmpty <==> |contents| == 0
  {}

  method Enqueue(t: T)
    requires Valid()
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents) + [t]
  {}

  method Front() returns (t: T)
    requires Valid()
    requires 0 < |contents|
    ensures t == contents[0]
  {}

  method Dequeue()
    requires Valid()
    requires 0 < |contents|
    modifies footprint
    ensures Valid() && fresh(footprint - old(footprint))
    ensures contents == old(contents)[1..]
  {}
}

class Node<T(0)> {}

////////TESTS////////

method TestIsEmpty1() {
  var queue := new Queue<int>.Init();
  var isEmpty := queue.IsEmpty();
  assert isEmpty == true;
}

method TestIsEmpty2() {
  var queue := new Queue<int>.Init();
  queue.Enqueue(5);
  var isEmpty := queue.IsEmpty();
  assert isEmpty == false;
}

method TestFront1() {
  var queue := new Queue<int>.Init();
  queue.Enqueue(42);
  var t := queue.Front();
  assert t == 42;
}

method TestFront2() {
  var queue := new Queue<int>.Init();
  queue.Enqueue(10);
  queue.Enqueue(20);
  var t := queue.Front();
  assert t == 10;
}
