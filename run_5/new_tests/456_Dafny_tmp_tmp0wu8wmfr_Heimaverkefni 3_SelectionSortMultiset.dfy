method MinOfMultiset( m: multiset<int> ) returns( min: int )
    requires m != multiset{};
    ensures min in m;
    ensures forall z | z in m :: min <= z;
{}

method Sort( m: multiset<int> ) returns ( s: seq<int> )
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
{}

////////TESTS////////

method TestMinOfMultiset1() {
  var m := multiset{5, 2, 8, 2, 1};
  var min := MinOfMultiset(m);
  assert min == 1;
}

method TestMinOfMultiset2() {
  var m := multiset{10, 15, 10};
  var min := MinOfMultiset(m);
  assert min == 10;
}

method TestSort1() {
  var m := multiset{3, 1, 4, 1, 5};
  var s := Sort(m);
  assert s == [1, 1, 3, 4, 5];
}

method TestSort2() {
  var m := multiset{7, 2, 9};
  var s := Sort(m);
  assert s == [2, 7, 9];
}
