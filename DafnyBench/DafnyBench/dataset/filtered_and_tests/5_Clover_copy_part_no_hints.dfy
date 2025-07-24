method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]
{}


method TestCopy1() {
  var src := new int[5];
  src[0], src[1], src[2], src[3], src[4] := 10, 20, 30, 40, 50;
  var dest := new int[7];
  dest[0], dest[1], dest[2], dest[3], dest[4], dest[5], dest[6] := 1, 2, 3, 4, 5, 6, 7;
  var r := copy(src, 1, dest, 2, 3);
  assert r.Length == 7;
  assert r[0] == 1 && r[1] == 2;
  assert r[2] == 20 && r[3] == 30 && r[4] == 40;
  assert r[5] == 6 && r[6] == 7;
}

method TestCopy2() {
  var src := new int[3];
  src[0], src[1], src[2] := 100, 200, 300;
  var dest := new int[4];
  dest[0], dest[1], dest[2], dest[3] := 0, 0, 0, 0;
  var r := copy(src, 0, dest, 1, 2);
  assert r.Length == 4;
  assert r[0] == 0;
  assert r[1] == 100 && r[2] == 200;
  assert r[3] == 0;
}
