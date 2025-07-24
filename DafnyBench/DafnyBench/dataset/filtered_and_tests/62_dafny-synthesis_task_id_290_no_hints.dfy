method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
    requires |lists| > 0
    ensures forall l :: l in lists ==> |l| <= |maxList|
    ensures maxList in lists
{}

method TestMaxLengthList1() {
  var lists := [[1, 2, 3], [4, 5], [6, 7, 8, 9]];
  var maxList := MaxLengthList(lists);
  assert maxList == [6, 7, 8, 9];
}

method TestMaxLengthList2() {
  var lists := [[1], [2, 3], [4]];
  var maxList := MaxLengthList(lists);
  assert maxList == [2, 3];
}
