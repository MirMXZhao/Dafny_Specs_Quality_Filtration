predicate quickSorted(Seq: seq<int>)
{}

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
{}

////////TESTS////////

method TestThreshold1() {
  var thres := 5;
  var Seq := [3, 7, 1, 9, 5, 2];
  var Seq_1, Seq_2 := threshold(thres, Seq);
  assert Seq_1 == [3, 1, 5, 2];
  assert Seq_2 == [7, 9, 5];
}

method TestThreshold2() {
  var thres := 0;
  var Seq := [-2, 3, -1, 0, 4];
  var Seq_1, Seq_2 := threshold(thres, Seq);
  assert Seq_1 == [-2, -1, 0];
  assert Seq_2 == [3, 0, 4];
}

method TestQuickSort1() {
  var Seq := [5, 2, 8, 1, 9];
  var Seq' := quickSort(Seq);
  assert Seq' == [1, 2, 5, 8, 9];
}

method TestQuickSort2() {
  var Seq := [3, 3, 1, 2];
  var Seq' := quickSort(Seq);
  assert Seq' == [1, 2, 3, 3];
}
