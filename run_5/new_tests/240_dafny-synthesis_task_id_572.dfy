method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{}

////////TESTS////////

method TestRemoveDuplicates1() {
  var a := new int[6] [1, 2, 2, 3, 1, 4];
  var result := RemoveDuplicates(a);
  assert result == [1, 2, 3, 4];
}

method TestRemoveDuplicates2() {
  var a := new int[4] [5, 5, 5, 5];
  var result := RemoveDuplicates(a);
  assert result == [5];
}
