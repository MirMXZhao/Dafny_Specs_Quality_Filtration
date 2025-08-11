method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}

////////TESTS////////

method TestRemoveDuplicates1() {
  var a := new int[5];
  a[0] := 1; a[1] := 2; a[2] := 2; a[3] := 3; a[4] := 1;
  var result := RemoveDuplicates(a);
  assert result == [1, 2, 3];
}

method TestRemoveDuplicates2() {
  var a := new int[4];
  a[0] := 5; a[1] := 5; a[2] := 5; a[3] := 5;
  var result := RemoveDuplicates(a);
  assert result == [5];
}
