method min(a: array<int>, n : int) returns (min : int)
    requires 0 < n <= a.Length;
	ensures (exists i : int :: 0 <= i && i < n && a[i] == min);
	ensures (forall i : int :: 0 <= i && i < n ==> a[i] >= min);
{}

////////TESTS////////

method TestMin1() {
  var a := new int[5];
  a[0] := 3;
  a[1] := 1;
  a[2] := 4;
  a[3] := 1;
  a[4] := 5;
  var result := min(a, 4);
  assert result == 1;
}

method TestMin2() {
  var a := new int[3];
  a[0] := 7;
  a[1] := 2;
  a[2] := 9;
  var result := min(a, 3);
  assert result == 2;
}
