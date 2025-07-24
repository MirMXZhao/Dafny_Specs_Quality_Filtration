// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Benchmark2 {
  method BinarySearch(a: array<int>, key: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j];
    ensures -1 <= result < a.Length;
    ensures 0 <= result ==> a[result] == key;
    ensures result == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key;
  {}
}

method Main() {}

method TestSearch(a: array<int>, key: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j];
{}



method TestBinarySearch1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 3, 5, 7, 9;
  var benchmark := new Benchmark2;
  var result := benchmark.BinarySearch(a, 5);
  assert result == 2;
}

method TestBinarySearch2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 2, 4, 6, 8;
  var benchmark := new Benchmark2;
  var result := benchmark.BinarySearch(a, 3);
  assert result == -1;
}
