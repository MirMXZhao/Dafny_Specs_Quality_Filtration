method Minimum(a: array<int>) returns (m: int) 
	requires a.Length > 0
	ensures exists i :: 0 <= i < a.Length && m == a[i]
	ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
{}

////////TESTS////////

method TestMinimum1() {
  var a := new int[4];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  a[3] := 1;
  var m := Minimum(a);
  assert m == 1;
}

method TestMinimum2() {
  var a := new int[3];
  a[0] := -3;
  a[1] := -1;
  a[2] := -5;
  var m := Minimum(a);
  assert m == -5;
}
