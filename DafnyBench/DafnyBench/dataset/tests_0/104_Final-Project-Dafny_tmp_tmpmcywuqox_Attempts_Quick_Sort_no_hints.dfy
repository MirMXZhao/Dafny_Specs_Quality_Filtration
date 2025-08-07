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

method testthreshold1() {
  var thres := 5;
  var Seq := [3, 7, 2, 8, 5, 1];
  var Seq_1, Seq_2 := threshold(thres, Seq);
  assert Seq_1 == [3, 2, 5, 1];
  assert Seq_2 == [7, 8, 5];
}

method testthreshold2() {
  var thres := 10;
  var Seq := [15, 8, 12, 3];
  var Seq_1, Seq_2 := threshold(thres, Seq);
  assert Seq_1 == [8, 3];
  assert Seq_2 == [15, 12];
}

method testthreshold3() {
  var thres := 0;
  var Seq := [-2, 3, -1, 5];
  var Seq_1, Seq_2 := threshold(thres, Seq);
  assert Seq_1 == [-2, -1];
  assert Seq_2 == [3, 0, 5];
}

method testLemma_11() {
  var Seq_1 := [1, 2, 3];
  var Seq_2 := [3, 1, 2];
  Lemma_1(Seq_1, Seq_2);
  assert 1 in Seq_2;
  assert 2 in Seq_2;
  assert 3 in Seq_2;
}

method testLemma_12() {
  var Seq_1 := [5, 5, 7];
  var Seq_2 := [7, 5, 5];
  Lemma_1(Seq_1, Seq_2);
  assert 5 in Seq_2;
  assert 7 in Seq_2;
}

method testquickSort1() {
  var Seq := [3, 1, 4, 1, 5];
  var Seq' := quickSort(Seq);
  assert Seq' == [1, 1, 3, 4, 5];
}

method testquickSort2() {
  var Seq := [7, 2, 9, 1];
  var Seq' := quickSort(Seq);
  assert Seq' == [1, 2, 7, 9];
}

method testquickSort3() {
  var Seq := [];
  var Seq' := quickSort(Seq);
  assert Seq' == [];
}
