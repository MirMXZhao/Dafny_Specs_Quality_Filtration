method TestArrayElements(a:array<int>, j: nat)
  requires 0<=j < a.Length
  modifies a
  ensures a[j] == 60
  ensures forall k :: 0 <= k < a.Length && k != j ==> a[k] == old(a[k])
{
  a[j] := 60;
}

////////TESTS////////

method TestTestArrayElements1() {
  var a := new int[3];
  a[0] := 10;
  a[1] := 20;
  a[2] := 30;
  TestArrayElements(a, 1);
  assert a[0] == 10;
  assert a[1] == 60;
  assert a[2] == 30;
}

method TestTestArrayElements2() {
  var a := new int[5];
  a[0] := 5;
  a[1] := 15;
  a[2] := 25;
  a[3] := 35;
  a[4] := 45;
  TestArrayElements(a, 0);
  assert a[0] == 60;
  assert a[1] == 15;
  assert a[2] == 25;
  assert a[3] == 35;
  assert a[4] == 45;
}
