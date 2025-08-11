method maxArray(a: array<int>) returns (m: int)
  requires a.Length >= 1
  ensures forall k :: 0 <= k < a.Length ==> m >= a[k]
  ensures exists k :: 0 <= k < a.Length && m == a[k]
{}

////////TESTS////////

method TestMaxArray1() {
  var a := new int[4];
  a[0] := 3;
  a[1] := 7;
  a[2] := 1;
  a[3] := 5;
  var m := maxArray(a);
  assert m == 7;
}

method TestMaxArray2() {
  var a := new int[3];
  a[0] := -2;
  a[1] := -8;
  a[2] := -1;
  var m := maxArray(a);
  assert m == -1;
}
