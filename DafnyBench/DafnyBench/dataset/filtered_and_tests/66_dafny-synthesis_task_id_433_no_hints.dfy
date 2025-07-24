method IsGreater(n: int, a: array<int>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
{}

method TestIsGreater1() {
  var a := new int[3];
  a[0] := 1; a[1] := 3; a[2] := 2;
  var result := IsGreater(5, a);
  assert result == true;
}

method TestIsGreater2() {
  var a := new int[3];
  a[0] := 1; a[1] := 7; a[2] := 2;
  var result := IsGreater(5, a);
  assert result == false;
}
