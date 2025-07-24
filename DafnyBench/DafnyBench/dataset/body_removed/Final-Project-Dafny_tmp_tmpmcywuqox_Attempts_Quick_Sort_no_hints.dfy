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






