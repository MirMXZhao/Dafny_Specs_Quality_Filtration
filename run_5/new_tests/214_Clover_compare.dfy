method Compare<T(==)>(a: T, b: T) returns (eq: bool)
  ensures a==b ==> eq==true
  ensures a!=b ==> eq==false
{}

////////TESTS////////

method TestCompare1() {
  var eq := Compare(5, 5);
  assert eq == true;
}

method TestCompare2() {
  var eq := Compare(3, 7);
  assert eq == false;
}
