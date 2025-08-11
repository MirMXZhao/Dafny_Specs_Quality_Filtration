method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]
{}

////////TESTS////////

method TestCopy1() {
  var src := new int[5];
  src[0], src[1], src[2], src[3], src[4] := 1, 2, 3, 4, 5;
  var dest := new int[4];
  dest[0], dest[1], dest[2], dest[3] := 10, 20, 30, 40;
  var r := copy(src, 1, dest, 0, 3);
  assert r.Length == 4;
  assert r[0] == 2 && r[1] == 3 && r[2] == 4 && r[3] == 40;
}

method TestCopy2() {
  var src := new int[3];
  src[0], src[1], src[2] := 7, 8, 9;
  var dest := new int[5];
  dest[0], dest[1], dest[2], dest[3], dest[4] := 1, 2, 3, 4, 5;
  var r := copy(src, 0, dest, 2, 2);
  assert r.Length == 5;
  assert r[0] == 1 && r[1] == 2 && r[2] == 7 && r[3] == 8 && r[4] == 5;
}
