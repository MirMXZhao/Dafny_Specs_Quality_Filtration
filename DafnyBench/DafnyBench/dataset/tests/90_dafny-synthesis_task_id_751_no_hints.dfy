method IsMinHeap(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length / 2 ==> a[i] <= a[2*i + 1] && (2*i + 2 == a.Length || a[i] <= a[2*i + 2])
    ensures !result ==> exists i :: 0 <= i < a.Length / 2 && (a[i] > a[2*i + 1] || (2*i + 2 != a.Length && a[i] > a[2*i + 2]))
{}

////////TESTS////////

method TestIsMinHeap1() {
  var a := new int[5];
  a[0] := 1;
  a[1] := 3;
  a[2] := 2;
  a[3] := 7;
  a[4] := 5;
  var result := IsMinHeap(a);
  assert result == true;
}

method TestIsMinHeap2() {
  var a := new int[4];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  a[3] := 1;
  var result := IsMinHeap(a);
  assert result == false;
}

method TestIsMinHeap3() {
  var a := new int[0];
  var result := IsMinHeap(a);
  assert result == true;
}

method TestIsMinHeap4() {
  var a := new int[1];
  a[0] := 42;
  var result := IsMinHeap(a);
  assert result == true;
}
