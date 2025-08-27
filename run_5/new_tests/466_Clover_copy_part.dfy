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
  var src := new int[4] [1, 2, 3, 4];
  var dest := new int[5] [10, 20, 30, 40, 50];
  var r := copy(src, 1, dest, 2, 2);
  assert r[..] == [10, 20, 2, 3, 50];
}

method TestCopy2() {
  var src := new int[3] [5, 6, 7];
  var dest := new int[4] [100, 200, 300, 400];
  var r := copy(src, 0, dest, 0, 3);
  assert r[..] == [5, 6, 7, 400];
}
