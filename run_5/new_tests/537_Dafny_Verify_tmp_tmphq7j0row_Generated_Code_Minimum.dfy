method Minimum(a: array<int>) returns (m: int) 
	requires a.Length > 0
	ensures exists i :: 0 <= i < a.Length && m == a[i]
	ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
{}

////////TESTS////////

method TestMinimum1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 5, 2, 8, 1;
  var m := Minimum(a);
  assert m == 1;
}

method TestMinimum2() {
  var a := new int[3];
  a[0], a[1], a[2] := 7, 3, 9;
  var m := Minimum(a);
  assert m == 3;
}
