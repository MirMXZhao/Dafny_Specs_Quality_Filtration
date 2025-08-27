method Tangent(r: array<int>, x: array<int>) returns (b: bool)
    requires forall i, j :: 0 <= i <= j < x.Length ==> x[i] <= x[j]
    requires forall i, j :: (0 <= i < r.Length && 0 <= j < x.Length) ==> (r[i] >= 0 && x[j] >= 0)
    ensures !b ==> forall i, j :: 0 <= i< r.Length && 0 <= j < x.Length ==> r[i] != x[j]   
    ensures b ==> exists i, j :: 0 <= i< r.Length && 0 <= j < x.Length && r[i] == x[j]
{}

////////TESTS////////

method TestTangent1() {
  var r := new int[3];
  r[0] := 1; r[1] := 3; r[2] := 5;
  var x := new int[4];
  x[0] := 2; x[1] := 3; x[2] := 4; x[3] := 6;
  var b := Tangent(r, x);
  assert b == true;
}

method TestTangent2() {
  var r := new int[2];
  r[0] := 1; r[1] := 7;
  var x := new int[3];
  x[0] := 2; x[1] := 4; x[2] := 6;
  var b := Tangent(r, x);
  assert b == false;
}
