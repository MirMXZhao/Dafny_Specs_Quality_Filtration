method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0;
    ensures p in m;
    ensures m == pre+multiset{p}+post;
    ensures forall z | z in pre :: z <= p;
    ensures forall z | z in post :: z >= p;
{}

method QuickSelect( m: multiset<int>, k: int )
        returns( pre: multiset<int>, kth: int, post: multiset<int> )
    decreases m;
    requires 0 <= k < |m|;
    ensures kth in m;
    ensures m == pre+multiset{kth}+post;
    ensures |pre| == k;
    ensures forall z | z in pre :: z <= kth;
    ensures forall z | z in post :: z >= kth;
{}

////////TESTS////////

method TestPartition1() {
  var m := multiset{5, 3, 8, 1};
  var pre, p, post := Partition(m);
  assert p in multiset{5, 3, 8, 1};
  assert multiset{5, 3, 8, 1} == pre + multiset{p} + post;
  assert forall z | z in pre :: z <= p;
  assert forall z | z in post :: z >= p;
}

method TestPartition2() {
  var m := multiset{7};
  var pre, p, post := Partition(m);
  assert p == 7;
  assert multiset{7} == pre + multiset{p} + post;
  assert forall z | z in pre :: z <= p;
  assert forall z | z in post :: z >= p;
}

method TestQuickSelect1() {
  var m := multiset{4, 2, 7, 1, 9};
  var k := 2;
  var pre, kth, post := QuickSelect(m, k);
  assert kth in multiset{4, 2, 7, 1, 9};
  assert multiset{4, 2, 7, 1, 9} == pre + multiset{kth} + post;
  assert |pre| == 2;
  assert forall z | z in pre :: z <= kth;
  assert forall z | z in post :: z >= kth;
}

method TestQuickSelect2() {
  var m := multiset{10, 5};
  var k := 0;
  var pre, kth, post := QuickSelect(m, k);
  assert kth in multiset{10, 5};
  assert multiset{10, 5} == pre + multiset{kth} + post;
  assert |pre| == 0;
  assert forall z | z in pre :: z <= kth;
  assert forall z | z in post :: z >= kth;
}
