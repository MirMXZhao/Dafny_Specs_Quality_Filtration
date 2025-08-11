method TriangularPrismVolume(base: int, height: int, length: int) returns (volume: int)
    requires base > 0
    requires height > 0
    requires length > 0
    ensures volume == (base * height * length) / 2
{}

////////TESTS////////

method TestTriangularPrismVolume1() {
    var volume := TriangularPrismVolume(6, 4, 10);
    assert volume == 120;
}

method TestTriangularPrismVolume2() {
    var volume := TriangularPrismVolume(8, 3, 5);
    assert volume == 60;
}
