method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
{}

////////TESTS////////

method TestInvertArray1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  InvertArray(a);
  assert a[0] == 4 && a[1] == 3 && a[2] == 2 && a[3] == 1;
}

method TestInvertArray2() {
  var a := new int[3];
  a[0] := 5; a[1] := 10; a[2] := 15;
  InvertArray(a);
  assert a[0] == 15 && a[1] == 10 && a[2] == 5;
}
