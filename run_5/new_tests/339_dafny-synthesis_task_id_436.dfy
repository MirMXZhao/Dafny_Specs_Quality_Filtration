predicate IsNegative(n: int)
{
    n < 0
}

method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
    ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
    ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
{}

////////TESTS////////

method TestFindNegativeNumbers1() {
  var arr := new int[5];
  arr[0] := -3;
  arr[1] := 5;
  arr[2] := -7;
  arr[3] := 2;
  arr[4] := -1;
  var negativeList := FindNegativeNumbers(arr);
  assert negativeList == [-3, -7, -1];
}

method TestFindNegativeNumbers2() {
  var arr := new int[4];
  arr[0] := 1;
  arr[1] := 3;
  arr[2] := 8;
  arr[3] := 10;
  var negativeList := FindNegativeNumbers(arr);
  assert negativeList == [];
}
