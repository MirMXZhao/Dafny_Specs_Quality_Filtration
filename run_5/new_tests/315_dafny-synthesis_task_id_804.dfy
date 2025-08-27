predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
{}

////////TESTS////////

method TestIsProductEven1() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 3;
  a[2] := 6;
  a[3] := 7;
  var result := IsProductEven(a);
  assert result == true;
}

method TestIsProductEven2() {
  var a := new int[3];
  a[0] := 1;
  a[1] := 3;
  a[2] := 5;
  var result := IsProductEven(a);
  assert result == false;
}
