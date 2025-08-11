method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
  requires index + |s| <= a.Length
  modifies a
  ensures a[..] == old(a[..index]) + s + old(a[index + |s|..])
{}

////////TESTS////////

method TestSeqIntoArray1() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 2, 3, 4, 5;
  var s := [10, 20];
  seqIntoArray(s, a, 1);
  assert a[..] == [1, 10, 20, 4, 5];
}

method TestSeqIntoArray2() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 7, 8, 9, 10;
  var s := [100];
  seqIntoArray(s, a, 0);
  assert a[..] == [100, 8, 9, 10];
}
