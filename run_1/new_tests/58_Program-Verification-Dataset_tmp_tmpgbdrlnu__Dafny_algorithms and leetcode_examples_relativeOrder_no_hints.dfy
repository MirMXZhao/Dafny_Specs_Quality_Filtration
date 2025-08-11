predicate IsEven (n: int)
{
  n % 2 == 0
}

method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
    ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{}

////////TESTS////////

method TestFindEvenNumbers1() {
  var arr := new int[5];
  arr[0] := 2;
  arr[1] := 3;
  arr[2] := 4;
  arr[3] := 5;
  arr[4] := 6;
  var evenNumbers := FindEvenNumbers(arr);
  assert evenNumbers[..] == [2, 4, 6];
}

method TestFindEvenNumbers2() {
  var arr := new int[4];
  arr[0] := 1;
  arr[1] := 3;
  arr[2] := 5;
  arr[3] := 7;
  var evenNumbers := FindEvenNumbers(arr);
  assert evenNumbers[..] == [];
}
