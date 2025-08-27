method Max(a:array<nat>)returns(m:int)
ensures a.Length > 0 ==> forall k :: 0<=k<a.Length ==> m >= a[k]
ensures a.Length == 0 ==> m == -1
ensures a.Length > 0 ==> m in a[..]
{}

////////TESTS////////

method TestMax1() {
  var a := new nat[4];
  a[0] := 3;
  a[1] := 7;
  a[2] := 2;
  a[3] := 9;
  var m := Max(a);
  assert m == 9;
}

method TestMax2() {
  var a := new nat[0];
  var m := Max(a);
  assert m == -1;
}
