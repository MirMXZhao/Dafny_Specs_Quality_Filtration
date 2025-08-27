function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{}

method sum_array( a: array<int>) returns (sum: int)
  requires a != null;
  ensures sum == sumTo(a, a.Length);
{}

////////TESTS////////

method TestSum_array1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var sum := sum_array(a);
  assert sum == 10;
}

method TestSum_array2() {
  var a := new int[3];
  a[0] := -1; a[1] := 5; a[2] := 2;
  var sum := sum_array(a);
  assert sum == 6;
}
