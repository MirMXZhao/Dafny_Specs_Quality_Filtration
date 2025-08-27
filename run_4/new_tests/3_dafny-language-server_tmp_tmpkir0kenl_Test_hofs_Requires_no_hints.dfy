predicate valid(x:int)
{
  x > 0
}

function ref1(y:int) : int
  requires valid(y);
{
  y - 1
}

lemma assumption1()
  ensures forall a, b :: valid(a) && valid(b) && ref1(a) == ref1(b) ==> a == b;
{
}

function {:opaque} ref2(y:int) : int
  requires valid(y);
{
  y - 1
}

lemma assumption2()
  ensures forall a, b :: valid(a) && valid(b) && ref2(a) == ref2(b) ==> a == b;
{
  reveal ref2();
}

////////TESTS////////

method testref11() {
  var x := 5;
  var result := ref1(x);
  assert result == 4;
}

method testref12() {
  var x := 10;
  var result := ref1(x);
  assert result == 9;
}

method testref21() {
  var x := 3;
  var result := ref2(x);
  assert result == 2;
}

method testref22() {
  var x := 7;
  var result := ref2(x);
  assert result == 6;
}
