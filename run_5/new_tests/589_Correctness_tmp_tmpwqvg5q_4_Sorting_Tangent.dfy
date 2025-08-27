method Tangent(r: array<int>, x: array<int>)
  returns (found: bool)
  requires forall i:: 1 <= i < x.Length ==> 
           x[i-1] < x[i]
  requires forall i, j ::
           0 <= i < j < x.Length ==>
           x[i] < x[j]
  ensures !found ==>
          forall i,j ::
          0 <= i < r.Length &&
          0 <= j < x.Length ==>
          r[i] != x[j]
  ensures found ==>
          exists i,j ::
          0 <= i < r.Length &&
          0 <= j < x.Length &&
          r[i] == x[j]
{}

method BinarySearch(a: array<int>, circle: int)
  returns (n: int)
  requires forall i ::
           1 <= i < a.Length
           ==> a[i-1] < a[i]
  requires forall i, j ::
           0 <= i < j < a.Length ==>
           a[i] < a[j]
  ensures 0 <= n <= a.Length
  ensures forall i ::
          0 <= i < n ==>
          a[i] < circle
  ensures forall i ::
          n <= i < a.Length ==>
          circle <= a[i]
{}

////////TESTS////////

method TestTangent1() {
  var r := new int[3];
  r[0] := 1; r[1] := 5; r[2] := 9;
  var x := new int[4];
  x[0] := 2; x[1] := 4; x[2] := 6; x[3] := 8;
  var found := Tangent(r, x);
  assert found == false;
}

method TestTangent2() {
  var r := new int[3];
  r[0] := 1; r[1] := 5; r[2] := 9;
  var x := new int[4];
  x[0] := 2; x[1] := 5; x[2] := 7; x[3] := 10;
  var found := Tangent(r, x);
  assert found == true;
}

method TestBinarySearch1() {
  var a := new int[5];
  a[0] := 1; a[1] := 3; a[2] := 5; a[3] := 7; a[4] := 9;
  var n := BinarySearch(a, 6);
  assert n == 3;
}

method TestBinarySearch2() {
  var a := new int[4];
  a[0] := 2; a[1] := 4; a[2] := 8; a[3] := 10;
  var n := BinarySearch(a, 1);
  assert n == 0;
}
