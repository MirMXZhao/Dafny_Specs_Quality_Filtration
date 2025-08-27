method AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
    ensures |r| == |l| + 1
    ensures r[|r| - 1] == t
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
{
    r := l + [t];
}

////////TESTS////////

method TestAddTupleToList1() {
  var l := [(1, 2), (3, 4)];
  var t := (5, 6);
  var r := AddTupleToList(l, t);
  assert r == [(1, 2), (3, 4), (5, 6)];
}

method TestAddTupleToList2() {
  var l := [];
  var t := (7, 8);
  var r := AddTupleToList(l, t);
  assert r == [(7, 8)];
}
