type intStack = seq<int>

function isEmpty(s: intStack): bool
{
    |s| == 0
}

function push(s: intStack, x: int): intStack
{
    s + [x]
}

function pop(s: intStack): intStack
requires !isEmpty(s)
{
   s[..|s|-1] 
}

////////TESTS////////

method TestisEmpty1() {
  var s := [1, 2, 3];
  var result := isEmpty(s);
  assert result == false;
}

method TestisEmpty2() {
  var s := [];
  var result := isEmpty(s);
  assert result == true;
}

method Testpush1() {
  var s := [1, 2, 3];
  var result := push(s, 4);
  assert result == [1, 2, 3, 4];
}

method Testpush2() {
  var s := [];
  var result := push(s, 5);
  assert result == [5];
}

method Testpop1() {
  var s := [1, 2, 3];
  var result := pop(s);
  assert result == [1, 2];
}

method Testpop2() {
  var s := [7];
  var result := pop(s);
  assert result == [];
}
