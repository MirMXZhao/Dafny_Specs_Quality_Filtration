method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]

{}

////////TESTS////////

method TestFindEvenNumbers1() {
  var arr := new int[5];
  arr[0] := 1;
  arr[1] := 2;
  arr[2] := 3;
  arr[3] := 4;
  arr[4] := 5;
  var evenNumbers := FindEvenNumbers(arr);
  assert evenNumbers[..] == [2, 4];
}

method TestFindEvenNumbers2() {
  var arr := new int[4];
  arr[0] := 10;
  arr[1] := 15;
  arr[2] := 20;
  arr[3] := 25;
  var evenNumbers := FindEvenNumbers(arr);
  assert evenNumbers[..] == [10, 20];
}
