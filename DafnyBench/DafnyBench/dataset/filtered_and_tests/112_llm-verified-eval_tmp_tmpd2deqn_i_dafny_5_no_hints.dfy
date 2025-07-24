method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
{}



method TestIntersperse1() {
  var numbers := [1, 2, 3];
  var delimiter := 4;
  var interspersed := intersperse(numbers, delimiter);
  assert interspersed == [1, 4, 2, 4, 3];
}

method TestIntersperse2() {
  var numbers := [];
  var delimiter := 5;
  var interspersed := intersperse(numbers, delimiter);
  assert interspersed == [];
}
