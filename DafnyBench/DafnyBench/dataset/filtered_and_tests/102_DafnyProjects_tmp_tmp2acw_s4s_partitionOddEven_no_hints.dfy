// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
method partitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])  
{}
 
predicate  odd(n: nat) { n % 2 == 1 }
predicate  even(n: nat) { n % 2 == 0 }

method testPartitionOddEven() {}



method TestPartitionOddEven1() {
  var a := new nat[5];
  a[0] := 2; a[1] := 3; a[2] := 4; a[3] := 5; a[4] := 6;
  partitionOddEven(a);
  assert multiset(a[..]) == multiset([2, 3, 4, 5, 6]);
  assert forall i, j :: 0 <= i < j < a.Length ==> !(even(a[i]) && odd(a[j]));
}

method TestPartitionOddEven2() {
  var a := new nat[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  partitionOddEven(a);
  assert multiset(a[..]) == multiset([1, 2, 3, 4]);
  assert forall i, j :: 0 <= i < j < a.Length ==> !(even(a[i]) && odd(a[j]));
}
