predicate IsOdd(n: int)
{
    n % 2 == 1
}

method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]))
{}

////////TESTS////////

method TestIsOddAtIndexOdd1() {
  var a := new int[4];
  a[0] := 2; a[1] := 3; a[2] := 4; a[3] := 7;
  var result := IsOddAtIndexOdd(a);
  assert result == true;
}

method TestIsOddAtIndexOdd2() {
  var a := new int[4];
  a[0] := 2; a[1] := 4; a[2] := 6; a[3] := 8;
  var result := IsOddAtIndexOdd(a);
  assert result == false;
}
