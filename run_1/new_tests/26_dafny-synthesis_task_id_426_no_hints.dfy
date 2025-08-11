predicate IsOdd(n: int)
{
    n % 2 != 0
}

method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{}

////////TESTS////////

method TestFilterOddNumbers1() {
  var arr := new int[5];
  arr[0] := 1;
  arr[1] := 2;
  arr[2] := 3;
  arr[3] := 4;
  arr[4] := 5;
  var oddList := FilterOddNumbers(arr);
  assert oddList == [1, 3, 5];
}

method TestFilterOddNumbers2() {
  var arr := new int[4];
  arr[0] := 2;
  arr[1] := 4;
  arr[2] := 6;
  arr[3] := 8;
  var oddList := FilterOddNumbers(arr);
  assert oddList == [];
}
