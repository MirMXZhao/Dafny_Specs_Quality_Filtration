method IsBreakEven(costPrice: int, sellingPrice: int) returns (result: bool)
    requires costPrice >= 0 && sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{}

////////TESTS////////

method TestIsBreakEven1() {
  var result := IsBreakEven(100, 100);
  assert result == true;
}

method TestIsBreakEven2() {
  var result := IsBreakEven(50, 75);
  assert result == false;
}
