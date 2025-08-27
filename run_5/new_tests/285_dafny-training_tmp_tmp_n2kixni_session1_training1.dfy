method abs(x: int) returns (y: int)
    ensures true
{}

method foo(x: int) 
    requires x >= 0
{}

method max(x: int, y: int) returns (m: int)
requires true;
ensures true;
{}

method ex1(n: int)
    requires true
    ensures true
{}

method foo2() 
    ensures false
    decreases *
{}

method find(a: seq<int>, key: int) returns (index: int)
    requires true
    ensures true
{}

method isPalindrome(a: seq<char>) returns (b: bool) 
{
    return true;
}

predicate sorted(a: seq<int>) 
{
    forall j, k::0 <= j < k < |a|  ==> a[j] <= a[k]
}

method unique(a: seq<int>) returns (b: seq<int>) 
    requires sorted(a)
    ensures true
{
  return a;
}

////////TESTS////////

method testabs1() {
  var y := abs(5);
  assert y == 5;
}

method testabs2() {
  var y := abs(-3);
  assert y == 3;
}

method testmax1() {
  var m := max(5, 3);
  assert m == 5;
}

method testmax2() {
  var m := max(2, 8);
  assert m == 8;
}

method testfind1() {
  var index := find([1, 2, 3, 4], 3);
  assert index == 2;
}

method testfind2() {
  var index := find([5, 10, 15], 20);
  assert index == -1;
}

method testisPalindrome1() {
  var b := isPalindrome(['a', 'b', 'a']);
  assert b == true;
}

method testisPalindrome2() {
  var b := isPalindrome(['x', 'y', 'z']);
  assert b == false;
}

method testunique1() {
  var b := unique([1, 2, 2, 3]);
  assert b == [1, 2, 3];
}

method testunique2() {
  var b := unique([5, 5, 5]);
  assert b == [5];
}
