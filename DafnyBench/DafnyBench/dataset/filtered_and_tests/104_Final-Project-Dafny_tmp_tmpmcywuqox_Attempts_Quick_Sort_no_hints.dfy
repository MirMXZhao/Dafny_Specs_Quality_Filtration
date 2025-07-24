predicate quickSorted(Seq: seq<int>)
{}

method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{}


lemma Lemma_1(Seq_1:seq,Seq_2:seq)  // The proof of the lemma is not necessary
  requires multiset(Seq_1) == multiset(Seq_2)
  ensures forall x | x in Seq_1 :: x in Seq_2

{}



method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
{}








method TestThreshold1() {
  var Seq := [5, 2, 8, 1, 9, 3];
  var thres := 5;
  var Seq_1, Seq_2 := threshold(thres, Seq);
  assert forall x | x in Seq_1 :: x <= 5;
  assert forall x | x in Seq_2 :: x >= 5;
  assert |Seq_1| + |Seq_2| == 6;
  assert multiset(Seq_1) + multiset(Seq_2) == multiset([5, 2, 8, 1, 9, 3]);
}

method TestThreshold2() {
  var Seq := [3, 7, 1, 4];
  var thres := 4;
  var Seq_1, Seq_2 := threshold(thres, Seq);
  assert forall x | x in Seq_1 :: x <= 4;
  assert forall x | x in Seq_2 :: x >= 4;
  assert |Seq_1| + |Seq_2| == 4;
  assert multiset(Seq_1) + multiset(Seq_2) == multiset([3, 7, 1, 4]);
}

method TestQuickSort1() {
  var Seq := [3, 1, 4, 1, 5];
  var Seq_prime := quickSort(Seq);
  assert multiset(Seq) == multiset(Seq_prime);
}

method TestQuickSort2() {
  var Seq := [9, 2, 7, 5];
  var Seq_prime := quickSort(Seq);
  assert multiset(Seq) == multiset(Seq_prime);
}
