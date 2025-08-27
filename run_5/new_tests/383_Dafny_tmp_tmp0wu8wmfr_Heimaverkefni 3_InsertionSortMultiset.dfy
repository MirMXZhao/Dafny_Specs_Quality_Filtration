method Search( s: seq<int>, x: int ) returns ( k: int )
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
    ensures 0 <= k <= |s|;
    ensures forall i | 0 <= i < k :: s[i] <= x;
    ensures forall i | k <= i < |s| :: s[i] >= x;
    ensures forall z | z in s[..k] :: z <= x;
    ensures forall z | z in s[k..] :: z >= x;
    ensures s == s[..k]+s[k..];
{}

method Sort( m: multiset<int> ) returns ( r: seq<int> )
    ensures multiset(r) == m;
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
{}

////////TESTS////////

method TestSearch1() {
  var s := [1, 3, 5, 7, 9];
  var k := Search(s, 4);
  assert k == 2;
}

method TestSearch2() {
  var s := [2, 4, 6, 8];
  var k := Search(s, 10);
  assert k == 4;
}

method TestSort1() {
  var m := multiset{3, 1, 4, 1, 5};
  var r := Sort(m);
  assert r == [1, 1, 3, 4, 5];
}

method TestSort2() {
  var m := multiset{7, 2, 9, 2};
  var r := Sort(m);
  assert r == [2, 2, 7, 9];
}
