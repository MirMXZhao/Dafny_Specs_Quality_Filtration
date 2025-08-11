method FindMax(a: array<int>) returns (max_idx: nat)
	requires a.Length > 0
	ensures 0 <= max_idx < a.Length
	ensures forall j :: 0 <= j < a.Length ==> a[max_idx] >= a[j]
{}

////////TESTS////////

method TestFindMax1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 7, 2, 9, 1;
  var max_idx := FindMax(a);
  assert max_idx == 3;
}

method TestFindMax2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 5, 5, 2, 5;
  var max_idx := FindMax(a);
  assert max_idx == 0 || max_idx == 1 || max_idx == 3;
}
