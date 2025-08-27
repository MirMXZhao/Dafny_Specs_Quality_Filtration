method remove_front(a:array<int>) returns (c:array<int>)
  requires a.Length>0
  ensures  a[1..] == c[..]
{}

////////TESTS////////

method TestRemoveFront1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var c := remove_front(a);
  assert c[..] == [2, 3, 4];
}

method TestRemoveFront2() {
  var a := new int[3];
  a[0] := 10; a[1] := 20; a[2] := 30;
  var c := remove_front(a);
  assert c[..] == [20, 30];
}
