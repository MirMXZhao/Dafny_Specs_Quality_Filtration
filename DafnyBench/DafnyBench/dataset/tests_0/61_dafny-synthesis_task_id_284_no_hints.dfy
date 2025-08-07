method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
    ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
{}

////////TESTS////////

method TestAllElementsEqual1() {
  var a := new int[4];
  a[0] := 5; a[1] := 5; a[2] := 5; a[3] := 5;
  var result := AllElementsEqual(a, 5);
  assert result == true;
}

method TestAllElementsEqual2() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 1;
  var result := AllElementsEqual(a, 1);
  assert result == false;
}

method TestAllElementsEqual3() {
  var a := new int[0];
  var result := AllElementsEqual(a, 42);
  assert result == true;
}
