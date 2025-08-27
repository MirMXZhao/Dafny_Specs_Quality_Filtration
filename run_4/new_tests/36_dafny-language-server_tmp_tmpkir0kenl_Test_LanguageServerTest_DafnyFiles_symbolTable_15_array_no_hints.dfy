method foo (s: seq<int>)
requires |s| > 1
{
    print s[1];
}

////////TESTS////////

method TestFoo1() {
  var s := [1, 2, 3];
  foo(s);
}

method TestFoo2() {
  var s := [5, 10];
  foo(s);
}
