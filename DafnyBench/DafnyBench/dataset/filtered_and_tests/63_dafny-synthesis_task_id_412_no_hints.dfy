/**
 * Remove odd numbers from an array of numbers
 **/

predicate IsEven(n: int)
{
    n % 2 == 0
}

method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)
    // All numbers in the output are even and exist in the input 
    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    // All even numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
{}

method TestRemoveOddNumbers1() {
  var arr := new int[5];
  arr[0] := 1; arr[1] := 2; arr[2] := 3; arr[3] := 4; arr[4] := 5;
  var evenList := RemoveOddNumbers(arr);
  assert evenList == [2, 4];
}

method TestRemoveOddNumbers2() {
  var arr := new int[4];
  arr[0] := 10; arr[1] := 15; arr[2] := 20; arr[3] := 25;
  var evenList := RemoveOddNumbers(arr);
  assert evenList == [10, 20];
}
