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
  var src := new int[4];
  src[0] := 1; src[1] := 2; src[2] := 3; src[3] := 4;
  var dest := new int[5];
  dest[0] := 0; dest[1] := 0; dest[2] := 0; dest[3] := 0; dest[4] := 0;
  var r := copy(src, 1, dest, 2, 2);
  assert r[0] == 0;
  assert r[1] == 0;
  assert r[2] == 2;
  assert r[3] == 3;
  assert r[4] == 0;
}

method TestCopy2() {
  var src := new int[3];
  src[0] := 10; src[1] := 20; src[2] := 30;
  var dest := new int[4];
  dest[0] := 5; dest[1] := 6; dest[2] := 7; dest[3] := 8;
  var r := copy(src, 0, dest, 1, 3);
  assert r[0] == 5;
  assert r[1] == 10;
  assert r[2] == 20;
  assert r[3] == 30;
}

method TestCopy3() {
  var src := new int[2];
  src[0] := 100; src[1] := 200;
  var dest := new int[2];
  dest[0] := 50; dest[1] := 60;
  var r := copy(src, 0, dest, 0, 0);
  assert r[0] == 50;
  assert r[1] == 60;
}
