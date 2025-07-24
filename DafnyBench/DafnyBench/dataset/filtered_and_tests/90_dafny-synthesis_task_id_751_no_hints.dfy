method IsMinHeap(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length / 2 ==> a[i] <= a[2*i + 1] && (2*i + 2 == a.Length || a[i] <= a[2*i + 2])
    ensures !result ==> exists i :: 0 <= i < a.Length / 2 && (a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]))
{}

method TestIsMinHeap1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 3, 2, 7, 4;
  var result := IsMinHeap(a);
  assert result == true;
}

method TestIsMinHeap2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 5, 3, 8, 2;
  var result := IsMinHeap(a);
  assert result == false;
}
