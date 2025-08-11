method findMax(a:array<int>) returns (pos:int, maxVal: int)
  requires a.Length > 0;
  requires forall i :: 0 <= i < a.Length ==> a[i] >= 0;
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= maxVal;
  ensures exists i :: 0 <= i < a.Length &&  a[i] == maxVal;
  ensures 0 <= pos < a.Length
  ensures a[pos] == maxVal;
{}

////////TESTS////////

method TestFindMax1() {
  var a := new int[4];
  a[0] := 3;
  a[1] := 7;
  a[2] := 2;
  a[3] := 7;
  var pos, maxVal := findMax(a);
  assert pos == 1 || pos == 3;
  assert maxVal == 7;
}

method TestFindMax2() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 1;
  a[2] := 3;
  var pos, maxVal := findMax(a);
  assert pos == 0;
  assert maxVal == 5;
}
