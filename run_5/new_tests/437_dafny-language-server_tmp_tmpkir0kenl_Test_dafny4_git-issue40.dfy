function SeqRepeat<T>(count:nat, elt:T) : seq<T>
    ensures |SeqRepeat<T>(count, elt)| == count
    ensures forall i :: 0 <= i < count ==> SeqRepeat<T>(count, elt)[i] == elt

datatype Maybe<T> = Nothing | Just(v: T)
type Num = x | 0 <= x < 10
datatype D = C(seq<Maybe<Num>>)

////////TESTS////////

method TestSeqRepeat1() {
  var result := SeqRepeat(3, 5);
  assert result == [5, 5, 5];
}

method TestSeqRepeat2() {
  var result := SeqRepeat(0, 10);
  assert result == [];
}
