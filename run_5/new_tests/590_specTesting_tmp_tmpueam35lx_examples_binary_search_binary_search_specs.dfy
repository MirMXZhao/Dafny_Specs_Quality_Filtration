lemma BinarySearch(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key
{}

predicate BinarySearchTransition(intSeq:seq<int>, key:int, r:int)
    requires (forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
}

lemma BinarySearchDeterministic(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key
    ensures r < 0 ==> r == -1
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key
{}

predicate BinarySearchDeterministicTransition(intSeq:seq<int>, key:int, r:int)
    requires (forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
    && (r < 0 ==> r == -1)
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong1(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | 0 < i < |intSeq| :: intSeq[i] != key
    ensures r < 0 ==> r == -1
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key

predicate BinarySearchWrong1Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | 0 < i < |intSeq| :: intSeq[i] != key)
    && (r < 0 ==> r == -1)
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong2(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key
    ensures r < 0 ==> r == -1
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key

predicate BinarySearchWrong2Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key)
    && (r < 0 ==> r == -1)
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

lemma BinarySearchWrong3(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r < 0 || (r < |intSeq| && intSeq[r] == key)
{
    return -1;
}

predicate BinarySearchWrong3Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    r < 0 || (r < |intSeq| && intSeq[r] == key)
}

lemma BinarySearchWrong4(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures 0 <= r < |intSeq| && intSeq[r] == key

predicate BinarySearchWrong4Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    0 <= r < |intSeq| && intSeq[r] == key
}

////////TESTS////////

method TestBinarySearch1() {
  var intSeq := [1, 3, 5, 7, 9];
  var key := 5;
  var r := BinarySearch(intSeq, key);
  assert r == 2;
}

method TestBinarySearch2() {
  var intSeq := [1, 3, 5, 7, 9];
  var key := 6;
  var r := BinarySearch(intSeq, key);
  assert r == -1;
}

method TestBinarySearchDeterministic1() {
  var intSeq := [2, 4, 6, 8, 10];
  var key := 6;
  var r := BinarySearchDeterministic(intSeq, key);
  assert r == 2;
}

method TestBinarySearchDeterministic2() {
  var intSeq := [2, 4, 6, 8, 10];
  var key := 5;
  var r := BinarySearchDeterministic(intSeq, key);
  assert r == -1;
}

method TestBinarySearchWrong11() {
  var intSeq := [1, 3, 5];
  var key := 3;
  var r := BinarySearchWrong1(intSeq, key);
  assert r == 1;
}

method TestBinarySearchWrong12() {
  var intSeq := [1, 3, 5];
  var key := 4;
  var r := BinarySearchWrong1(intSeq, key);
  assert r == -1;
}

method TestBinarySearchWrong21() {
  var intSeq := [1, 3, 5, 7];
  var key := 5;
  var r := BinarySearchWrong2(intSeq, key);
  assert r == 2;
}

method TestBinarySearchWrong22() {
  var intSeq := [1, 3, 5, 7];
  var key := 6;
  var r := BinarySearchWrong2(intSeq, key);
  assert r == -1;
}

method TestBinarySearchWrong31() {
  var intSeq := [1, 2, 3];
  var key := 2;
  var r := BinarySearchWrong3(intSeq, key);
  assert r == -1;
}

method TestBinarySearchWrong32() {
  var intSeq := [5, 10, 15];
  var key := 20;
  var r := BinarySearchWrong3(intSeq, key);
  assert r == -1;
}

method TestBinarySearchWrong41() {
  var intSeq := [1, 4, 7, 10];
  var key := 7;
  var r := BinarySearchWrong4(intSeq, key);
  assert r == 2;
}

method TestBinarySearchWrong42() {
  var intSeq := [2, 6, 8, 12];
  var key := 6;
  var r := BinarySearchWrong4(intSeq, key);
  assert r == 1;
}
