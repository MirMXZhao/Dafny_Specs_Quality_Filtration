function min(a: int, b: int): int
    ensures min(a, b) <= a && min(a, b) <= b
    ensures min(a, b) == a || min(a, b) == b
{}

method minMethod(a: int, b: int) returns (c: int)
    ensures c <= a && c <= b
    ensures c == a || c == b
    ensures c == min(a, b)
{}

ghost function minFunction(a: int, b: int): int
    ensures minFunction(a, b) <= a && minFunction(a, b) <= b
    ensures minFunction(a, b) == a || minFunction(a, b) == b
{}

method minArray(a: array<int>) returns (m: int)
    requires a!= null  && a.Length > 0 ;
    ensures forall k | 0 <= k < a.Length :: m <= a[k]
    ensures exists k | 0 <= k < a.Length :: m == a[k]
{}

////////TESTS////////

method TestMin1() {
  var result := min(5, 3);
  assert result == 3;
}

method TestMin2() {
  var result := min(-2, 7);
  assert result == -2;
}

method TestMinMethod1() {
  var c := minMethod(10, 15);
  assert c == 10;
}

method TestMinMethod2() {
  var c := minMethod(-5, -8);
  assert c == -8;
}

method TestMinFunction1() {
  var result := minFunction(4, 9);
  assert result == 4;
}

method TestMinFunction2() {
  var result := minFunction(12, 6);
  assert result == 6;
}

method TestMinArray1() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  var m := minArray(a);
  assert m == 2;
}

method TestMinArray2() {
  var a := new int[4];
  a[0] := -1;
  a[1] := 3;
  a[2] := -5;
  a[3] := 7;
  var m := minArray(a);
  assert m == -5;
}
