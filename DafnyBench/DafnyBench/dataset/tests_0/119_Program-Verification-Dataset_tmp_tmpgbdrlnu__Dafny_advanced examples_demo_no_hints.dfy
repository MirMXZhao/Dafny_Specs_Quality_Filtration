method Partition(a: array<int>) returns (lo: int, hi: int)
  modifies a
  ensures 0 <= lo <= hi <= a.Length
  ensures forall x | 0 <= x < lo :: a[x] < 0
  ensures forall x | lo <= x < hi :: a[x] == 0
  ensures forall x | hi <= x < a.Length :: a[x] > 0
{}

////////TESTS////////

method TestPartition1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := -2, 0, 3, -1, 0;
  var lo, hi := Partition(a);
  assert lo == 2;
  assert hi == 4;
}

method TestPartition2() {
  var a := new int[3];
  a[0], a[1], a[2] := 1, 2, 3;
  var lo, hi := Partition(a);
  assert lo == 0;
  assert hi == 0;
}

method TestPartition3() {
  var a := new int[0];
  var lo, hi := Partition(a);
  assert lo == 0;
  assert hi == 0;
}
