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

method Testvalid1() {
  var result := valid(5);
  assert result == true;
}

method Testvalid2() {
  var result := valid(0);
  assert result == false;
}

method Testref11() {
  var result := ref1(3);
  assert result == 2;
}

method Testref12() {
  var result := ref1(10);
  assert result == 9;
}

method Testref21() {
  var result := ref2(7);
  assert result == 6;
}

method Testref22() {
  var result := ref2(1);
  assert result == 0;
}
