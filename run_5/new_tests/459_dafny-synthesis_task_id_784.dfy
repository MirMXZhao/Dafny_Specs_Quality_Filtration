predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

predicate IsFirstEven(evenIndex: int, lst: seq<int>)
    requires 0 <= evenIndex < |lst|
    requires IsEven(lst[evenIndex])
{}

predicate IsFirstOdd(oddIndex: int, lst: seq<int>)
    requires 0 <= oddIndex < |lst|
    requires IsOdd(lst[oddIndex])
{}


method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: int, oddIndex : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures 0 <= evenIndex < |lst|
    ensures 0 <= oddIndex < |lst|
    ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
    ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{}

method ProductEvenOdd(lst: seq<int>) returns (product : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 
                           0 <= j < |lst| && IsOdd(lst[j])  && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
{}

////////TESTS////////

method TestFirstEvenOddIndices1() {
    var lst := [3, 4, 5, 6];
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    assert evenIndex == 1;
    assert oddIndex == 0;
}

method TestFirstEvenOddIndices2() {
    var lst := [2, 1, 8, 9];
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    assert evenIndex == 0;
    assert oddIndex == 1;
}

method TestProductEvenOdd1() {
    var lst := [3, 4, 5, 6];
    var product := ProductEvenOdd(lst);
    assert product == 12;
}

method TestProductEvenOdd2() {
    var lst := [2, 1, 8, 9];
    var product := ProductEvenOdd(lst);
    assert product == 2;
}
