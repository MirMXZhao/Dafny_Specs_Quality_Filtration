predicate IsOdd(x: int)
{
    x % 2 != 0
}

method FindFirstOdd(a: array<int>) returns (found: bool, index: int)
    requires a != null
    ensures !found ==> forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
    ensures found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i])
{}

////////TESTS////////

method TestFindFirstOdd1() {
    var a := new int[4];
    a[0] := 2; a[1] := 4; a[2] := 7; a[3] := 8;
    var found, index := FindFirstOdd(a);
    assert found == true;
    assert index == 2;
}

method TestFindFirstOdd2() {
    var a := new int[3];
    a[0] := 2; a[1] := 4; a[2] := 6;
    var found, index := FindFirstOdd(a);
    assert found == false;
    assert index == 0;
}

method TestFindFirstOdd3() {
    var a := new int[1];
    a[0] := 3;
    var found, index := FindFirstOdd(a);
    assert found == true;
    assert index == 0;
}

method TestFindFirstOdd4() {
    var a := new int[0];
    var found, index := FindFirstOdd(a);
    assert found == false;
    assert index == 0;
}
