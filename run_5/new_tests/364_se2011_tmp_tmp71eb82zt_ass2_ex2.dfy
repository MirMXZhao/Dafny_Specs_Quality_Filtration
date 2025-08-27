method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
{}

////////TESTS////////

method TestSecondLargest1() {
  var a := new int[4];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  a[3] := 1;
  var seclar := SecondLargest(a);
  assert seclar == 5;
}

method TestSecondLargest2() {
  var a := new int[3];
  a[0] := 10;
  a[1] := 20;
  a[2] := 15;
  var seclar := SecondLargest(a);
  assert seclar == 15;
}
