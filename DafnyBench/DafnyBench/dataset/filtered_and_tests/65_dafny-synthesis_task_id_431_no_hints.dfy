method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires a != null && b != null
    ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
{}

method TestHasCommonElement1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var b := new int[2];
  b[0] := 3; b[1] := 4;
  var result := HasCommonElement(a, b);
  assert result == true;
}

method TestHasCommonElement2() {
  var a := new int[2];
  a[0] := 1; a[1] := 2;
  var b := new int[2];
  b[0] := 3; b[1] := 4;
  var result := HasCommonElement(a, b);
  assert result == false;
}
