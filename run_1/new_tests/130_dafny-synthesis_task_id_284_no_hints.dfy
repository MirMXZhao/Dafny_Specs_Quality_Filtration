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
  a[0] := 2; a[1] := 3; a[2] := 2;
  var result := AllElementsEqual(a, 2);
  assert result == false;
}
