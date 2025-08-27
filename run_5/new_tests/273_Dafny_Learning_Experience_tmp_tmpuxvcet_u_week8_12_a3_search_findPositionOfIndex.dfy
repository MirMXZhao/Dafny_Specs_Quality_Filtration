method FindPositionOfElement(a:array<int>,Element:nat,n1:nat,s1:seq<int>) returns (Position:int,Count:nat)
        requires n1 == |s1| && 0 <= n1 <= a.Length
        requires forall i:: 0<= i < |s1| ==> a[i] == s1[i]
        ensures Position == -1 || Position >= 1
        ensures |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
{}

////////TESTS////////

method TestFindPositionOfElement1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var s1 := [1, 2, 3, 4];
  var Position, Count := FindPositionOfElement(a, 3, 4, s1);
  assert Position == 3;
  assert Count == 1;
}

method TestFindPositionOfElement2() {
  var a := new int[0];
  var s1 := [];
  var Position, Count := FindPositionOfElement(a, 5, 0, s1);
  assert Position == -1;
  assert Count == 0;
}
