method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
{}

////////TESTS////////

method TestAppend1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var c := append(a, 4);
  assert c[..] == [1, 2, 3, 4];
}

method TestAppend2() {
  var a := new int[0];
  var c := append(a, 5);
  assert c[..] == [5];
}
