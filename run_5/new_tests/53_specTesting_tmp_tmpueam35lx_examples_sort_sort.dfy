method quickSort(intSeq:array<int>)
    modifies intSeq
    ensures forall i:nat, j:nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]


lemma sort(prevSeq:seq<int>) returns (curSeq:seq<int>)
    ensures (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    ensures multiset(prevSeq) == multiset(curSeq)

predicate post_sort(prevSeq:seq<int>, curSeq:seq<int>)
{
    && (forall i:nat, j:nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j])
    && multiset(prevSeq) == multiset(curSeq)
}

lemma multisetAdditivity(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
    requires m1 == m2 + m3
    requires m1 == m2 + m4
    ensures m3 == m4
    {}

lemma twoSortedSequencesWithSameElementsAreEqual(s1:seq<int>, s2:seq<int>)
    requires (forall i:nat, j:nat | 0 <= i <= j < |s1| :: s1[i] <= s1[j])
    requires (forall i:nat, j:nat | 0 <= i <= j < |s2| :: s2[i] <= s2[j])
    requires multiset(s1) == multiset(s2)
    requires |s1| == |s2|
    ensures s1 == s2
{}

lemma sort_determinisitc(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{}

lemma sort_determinisitc1(prevSeq:seq<int>, curSeq:seq<int>, curSeq':seq<int>)
    requires prevSeq == [5,4,3,2,1]
    requires post_sort(prevSeq, curSeq)
    requires post_sort(prevSeq, curSeq')
    ensures curSeq == curSeq'
{
}

////////TESTS////////

method testquickSort1() {
  var intSeq := new int[5];
  intSeq[0] := 5;
  intSeq[1] := 2;
  intSeq[2] := 8;
  intSeq[3] := 1;
  intSeq[4] := 9;
  quickSort(intSeq);
  assert intSeq[0] == 1;
  assert intSeq[1] == 2;
  assert intSeq[2] == 5;
  assert intSeq[3] == 8;
  assert intSeq[4] == 9;
}

method testquickSort2() {
  var intSeq := new int[3];
  intSeq[0] := 3;
  intSeq[1] := 1;
  intSeq[2] := 2;
  quickSort(intSeq);
  assert intSeq[0] == 1;
  assert intSeq[1] == 2;
  assert intSeq[2] == 3;
}

method testsort1() {
  var prevSeq := [4, 1, 3, 2];
  var curSeq := sort(prevSeq);
  assert curSeq == [1, 2, 3, 4];
}

method testsort2() {
  var prevSeq := [7, 3, 9, 1, 5];
  var curSeq := sort(prevSeq);
  assert curSeq == [1, 3, 5, 7, 9];
}
