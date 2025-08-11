predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
{}

////////TESTS////////

method TestIsEvenAtIndexEven1() {
    var lst := [2, 3, 4, 7, 8];
    var result := IsEvenAtIndexEven(lst);
    assert result == true;
}

method TestIsEvenAtIndexEven2() {
    var lst := [1, 3, 4, 7, 8];
    var result := IsEvenAtIndexEven(lst);
    assert result == false;
}
