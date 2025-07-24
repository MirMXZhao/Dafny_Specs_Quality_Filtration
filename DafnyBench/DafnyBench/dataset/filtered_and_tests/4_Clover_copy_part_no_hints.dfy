method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]
{}


method TestCopy1() {
  var src := new int[4] [1, 2, 3, 4];
  var dest := new int[5] [0, 0, 0, 0, 0];
  var r := copy(src, 1, dest, 2, 2);
  assert r.Length == 5;
  assert r[..2] == [0, 0];
  assert r[4..] == [0];
  assert r[2..4] == [2, 3];
}

method TestCopy2() {
  var src := new int[3] [10, 20, 30];
  var dest := new int[6] [1, 2, 3, 4, 5, 6];
  var r := copy(src, 0, dest, 1, 3);
  assert r.Length == 6;
  assert r[..1] == [1];
  assert r[4..] == [5, 6];
  assert r[1..4] == [10, 20, 30];
}
