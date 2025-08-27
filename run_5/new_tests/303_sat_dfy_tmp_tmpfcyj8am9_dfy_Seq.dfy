module Seq {
    function seq_sum(s: seq<int>) : (sum: int)
    {}

    lemma SeqPartsSameSum(s: seq<int>, s1: seq<int>, s2: seq<int>)
        requires s == s1 + s2
        ensures seq_sum(s) == seq_sum(s1) + seq_sum(s2)
    {}

    lemma DifferentPermutationSameSum(s1: seq<int>, s2: seq<int>)
        requires multiset(s1) == multiset(s2)
        ensures seq_sum(s1) == seq_sum(s2)
    {}

}

////////TESTS////////

method TestSeqSum1() {
  var s := [1, 2, 3, 4];
  var sum := Seq.seq_sum(s);
  assert sum == 10;
}

method TestSeqSum2() {
  var s := [-2, 5, -1, 3];
  var sum := Seq.seq_sum(s);
  assert sum == 5;
}
