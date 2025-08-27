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
  a[2] := 1;
  a[3] := 5;
  var pos, maxVal := findMax(a);
  assert pos == 1;
  assert maxVal == 7;
}

method TestFindMax2() {
  var a := new int[3];
  a[0] := 10;
  a[1] := 2;
  a[2] := 8;
  var pos, maxVal := findMax(a);
  assert pos == 0;
  assert maxVal == 10;
}
