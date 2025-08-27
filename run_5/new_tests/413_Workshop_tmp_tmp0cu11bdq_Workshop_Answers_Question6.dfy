method arrayUpToN(n: int) returns (a: array<int>)
    requires n >= 0
    ensures a.Length == n
    ensures forall j :: 0 < j < n ==> a[j] >= 0
    ensures forall j, k : int :: 0 <= j <= k < n ==> a[j] <= a[k]
{}

////////TESTS////////

method TestarrayUpToN1() {
  var a := arrayUpToN(5);
  assert a.Length == 5;
  assert forall j :: 0 < j < 5 ==> a[j] >= 0;
  assert forall j, k : int :: 0 <= j <= k < 5 ==> a[j] <= a[k];
}

method TestarrayUpToN2() {
  var a := arrayUpToN(0);
  assert a.Length == 0;
  assert forall j :: 0 < j < 0 ==> a[j] >= 0;
  assert forall j, k : int :: 0 <= j <= k < 0 ==> a[j] <= a[k];
}
