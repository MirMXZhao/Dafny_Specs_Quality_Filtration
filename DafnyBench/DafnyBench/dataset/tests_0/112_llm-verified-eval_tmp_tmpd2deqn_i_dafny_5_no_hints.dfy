method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
{}

////////TESTS////////

method testintersperse1() {
  var numbers := [1, 2, 3];
  var interspersed := intersperse(numbers, 4);
  assert interspersed == [1, 4, 2, 4, 3];
}

method testintersperse2() {
  var numbers := [];
  var interspersed := intersperse(numbers, 5);
  assert interspersed == [];
}

method testintersperse3() {
  var numbers := [7];
  var interspersed := intersperse(numbers, 9);
  assert interspersed == [7];
}
