lemma SkippingLemma(a : array<int>, j : int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   requires 0 <= j < a.Length
   ensures forall k :: j <= k < j + a[j] && k < a.Length ==> a[k] != 0
{}
method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
{}

////////TESTS////////

method TestFindZero1() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 2;
  a[2] := 0;
  a[3] := 1;
  var index := FindZero(a);
  assert index == 2;
}

method TestFindZero2() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  var index := FindZero(a);
  assert index < 0;
}

method TestFindZero3() {
  var a := new int[1];
  a[0] := 0;
  var index := FindZero(a);
  assert index == 0;
}
