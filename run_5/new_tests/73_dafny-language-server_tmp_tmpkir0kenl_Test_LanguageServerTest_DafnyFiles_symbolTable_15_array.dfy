method foo (s: seq<int>)
requires |s| > 1
{
    print s[1];
}

////////TESTS////////

method TestFoo1() {
  foo([1, 2, 3]);
}

method TestFoo2() {
  foo([5, 10]);
}
