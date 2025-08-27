/*
HumanEvalX 9
From a given list of integers, generate a list of rolling maximum element found until given moment in the sequence.
*/

function isMax(m: int, numbers: seq<int>): bool
{}

method max(numbers: seq<int>) returns (result: int)
requires numbers != []
ensures isMax(result, numbers)
{}

method RollingMax(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{}