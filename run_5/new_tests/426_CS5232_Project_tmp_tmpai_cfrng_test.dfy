iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{}

////////TESTS////////

method TestGen1() {
  var it := new Gen(5);
  var more := it.MoveNext();
  if more {
    assert it.x == 5;
  }
}

method TestGen2() {
  var it := new Gen(-3);
  var more := it.MoveNext();
  if more {
    assert it.x == -3;
  }
}
