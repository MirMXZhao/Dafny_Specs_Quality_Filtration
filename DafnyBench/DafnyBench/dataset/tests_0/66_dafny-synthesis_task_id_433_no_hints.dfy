method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
{}

////////TESTS////////

method TestIsGreater1() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 3;
  a[2] := 5;
  var result := IsGreater(6, a);
  assert result == true;
}

method TestIsGreater2() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 8;
  a[2] := 3;
  var result := IsGreater(5, a);
  assert result == false;
}

method TestIsGreater3() {
  var a := new int[0];
  var result := IsGreater(10, a);
  assert result == true;
}

method TestIsGreater4() {
  var a := new int[2];
  a[0] := 5;
  a[1] := 5;
  var result := IsGreater(5, a);
  assert result == false;
}
