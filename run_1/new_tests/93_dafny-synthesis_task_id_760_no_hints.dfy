method HasOnlyOneDistinctElement(a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] == a[j]
    ensures !result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && a[i] != a[j]
{}

////////TESTS////////

method TestHasOnlyOneDistinctElement1() {
  var a := new int[4];
  a[0] := 5;
  a[1] := 5;
  a[2] := 5;
  a[3] := 5;
  var result := HasOnlyOneDistinctElement(a);
  assert result == true;
}

method TestHasOnlyOneDistinctElement2() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 2;
  a[2] := 1;
  var result := HasOnlyOneDistinctElement(a);
  assert result == false;
}
