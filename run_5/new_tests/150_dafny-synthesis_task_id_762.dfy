method IsMonthWith30Days(month: int) returns (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month == 4 || month == 6 || month == 9 || month == 11
{}

////////TESTS////////

method TestIsMonthWith30Days1() {
  var result := IsMonthWith30Days(4);
  assert result == true;
}

method TestIsMonthWith30Days2() {
  var result := IsMonthWith30Days(1);
  assert result == false;
}
