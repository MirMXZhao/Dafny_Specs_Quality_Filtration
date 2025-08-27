predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method Intersection(a: array<int>, b: array<int>) returns (result: seq<int>)
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}

////////TESTS////////

method TestIntersection1() {
  var a := new int[3] := [1, 2, 3];
  var b := new int[3] := [2, 3, 4];
  var result := Intersection(a, b);
  assert result == [2, 3] || result == [3, 2];
}

method TestIntersection2() {
  var a := new int[2] := [5, 7];
  var b := new int[2] := [1, 9];
  var result := Intersection(a, b);
  assert result == [];
}
