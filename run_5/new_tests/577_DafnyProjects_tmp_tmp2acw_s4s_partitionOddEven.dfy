method partitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])  
{}
 
predicate  odd(n: nat) { n % 2 == 1 }
predicate  even(n: nat) { n % 2 == 0 }

////////TESTS////////

method TestPartitionOddEven1() {
  var a := new nat[4];
  a[0], a[1], a[2], a[3] := 1, 2, 3, 4;
  var old_multiset := multiset(a[..]);
  partitionOddEven(a);
  assert multiset(a[..]) == old_multiset;
  assert forall i, j :: 0 <= i < j < a.Length ==> !(even(a[i]) && odd(a[j]));
}

method TestPartitionOddEven2() {
  var a := new nat[3];
  a[0], a[1], a[2] := 5, 7, 9;
  var old_multiset := multiset(a[..]);
  partitionOddEven(a);
  assert multiset(a[..]) == old_multiset;
  assert forall i, j :: 0 <= i < j < a.Length ==> !(even(a[i]) && odd(a[j]));
}
