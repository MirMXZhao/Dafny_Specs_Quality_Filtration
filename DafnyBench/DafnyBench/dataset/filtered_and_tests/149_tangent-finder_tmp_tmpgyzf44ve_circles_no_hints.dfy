method Tangent(r: array<int>, x: array<int>) returns (b: bool)
    requires forall i, j :: 0 <= i <= j < x.Length ==> x[i] <= x[j] // values in x will be in ascending order or empty
    requires forall i, j :: (0 <= i < r.Length && 0 <= j < x.Length) ==> (r[i] >= 0 && x[j] >= 0)       // x and r will contain no negative values
    ensures !b ==> forall i, j :: 0 <= i< r.Length && 0 <= j < x.Length ==> r[i] != x[j]   
    ensures b ==> exists i, j :: 0 <= i< r.Length && 0 <= j < x.Length && r[i] == x[j]
{}


method TestTangent1() {
  var r := new int[3];
  r[0] := 1; r[1] := 3; r[2] := 5;
  var x := new int[2];
  x[0] := 2; x[1] := 4;
  var b := Tangent(r, x);
  assert b == false;
}

method TestTangent2() {
  var r := new int[3];
  r[0] := 1; r[1] := 3; r[2] := 5;
  var x := new int[3];
  x[0] := 1; x[1] := 2; x[2] := 6;
  var b := Tangent(r, x);
  assert b == true;
}
