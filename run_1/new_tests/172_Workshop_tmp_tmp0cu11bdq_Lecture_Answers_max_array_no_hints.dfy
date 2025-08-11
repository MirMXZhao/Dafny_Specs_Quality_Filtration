method max(a:array<int>) returns(max:int)
    requires a != null;
    ensures forall j :: j >= 0 && j < a.Length ==> max >= a[j];
    ensures a.Length > 0 ==> exists j :: j >= 0 && j < a.Length && max == a[j];
{}

////////TESTS////////

method TestMax1() {
  var a := new int[4];
  a[0] := 3;
  a[1] := 7;
  a[2] := 1;
  a[3] := 5;
  var max_val := max(a);
  assert max_val == 7;
}

method TestMax2() {
  var a := new int[3];
  a[0] := -2;
  a[1] := -8;
  a[2] := -1;
  var max_val := max(a);
  assert max_val == -1;
}
