predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{}

lemma Lemma_1(Seq_1:seq,Seq_2:seq)
  requires multiset(Seq_1) == multiset(Seq_2)
  ensures forall x | x in Seq_1 :: x in Seq_2
{}

method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
  decreases |Seq|
{}

////////TESTS////////

method TestThreshold1() {
  var thres := 5;
  var Seq := [1, 3, 7, 2, 9, 4, 6];
  var Seq_1, Seq_2 := threshold(thres, Seq);
  assert Seq_1 == [1, 3, 2, 4, 5];
  assert Seq_2 == [7, 9, 6, 5];
}

method TestThreshold2() {
  var thres := 10;
  var Seq := [1, 5, 15, 3, 12];
  var Seq_1, Seq_2 := threshold(thres, Seq);
  assert Seq_1 == [1, 5, 3, 10];
  assert Seq_2 == [15, 12, 10];
}

method TestQuickSort1() {
  var Seq := [3, 1, 4, 1, 5];
  var Seq' := quickSort(Seq);
  assert Seq' == [1, 1, 3, 4, 5];
}

method TestQuickSort2() {
  var Seq := [9, 2, 7, 1, 8];
  var Seq' := quickSort(Seq);
  assert Seq' == [1, 2, 7, 8, 9];
}
