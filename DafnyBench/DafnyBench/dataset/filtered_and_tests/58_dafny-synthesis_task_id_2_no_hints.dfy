predicate InArray(a: array<int>, x: int)
    reads a
{}

method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}

method TestSharedElements1() {
  var a := new int[3];
  a[0] := 1; a[1] := 2; a[2] := 3;
  var b := new int[3];
  b[0] := 2; b[1] := 3; b[2] := 4;
  var result := SharedElements(a, b);
  assert result == [2, 3] || result == [3, 2];
}

method TestSharedElements2() {
  var a := new int[2];
  a[0] := 1; a[1] := 5;
  var b := new int[2];
  b[0] := 2; b[1] := 4;
  var result := SharedElements(a, b);
  assert result == [];
}
