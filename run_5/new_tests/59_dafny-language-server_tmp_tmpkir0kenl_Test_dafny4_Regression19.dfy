predicate ContainsNothingBut5(s: set<int>)
{
  forall q :: q in s ==> q == 5
}

predicate YeahContains5(s: set<int>)
{
  exists q :: q in s && q == 5
}

predicate ViaSetComprehension(s: set<int>) {
  |set q | q in s && q == 5| != 0
}

predicate LambdaTest(s: set<int>) {
  (q => q in s)(5)
}

predicate ViaMapComprehension(s: set<int>) {
  |(map q | q in s && q == 5 :: true).Keys| != 0
}

predicate Contains5(s: set<int>)
{
  var q := 5; q in s
}

datatype R = MakeR(int) | Other

predicate RIs5(r: R) {
  match r case MakeR(q) => q == 5 case Other => false
}

lemma NonemptySet(x: int, s: set<int>)
  requires x in s
  ensures |s| != 0
{
}
lemma NonemptyMap(x: int, s: map<int,bool>)
  requires x in s.Keys
  ensures |s| != 0
{
}

////////TESTS////////

method TestContainsNothingBut51() {
  var s := {5, 5, 5};
  var result := ContainsNothingBut5(s);
  assert result == true;
}

method TestContainsNothingBut52() {
  var s := {5, 3, 7};
  var result := ContainsNothingBut5(s);
  assert result == false;
}

method TestYeahContains51() {
  var s := {1, 5, 9};
  var result := YeahContains5(s);
  assert result == true;
}

method TestYeahContains52() {
  var s := {1, 2, 3};
  var result := YeahContains5(s);
  assert result == false;
}

method TestViaSetComprehension1() {
  var s := {5, 10, 15};
  var result := ViaSetComprehension(s);
  assert result == true;
}

method TestViaSetComprehension2() {
  var s := {1, 2, 3};
  var result := ViaSetComprehension(s);
  assert result == false;
}

method TestLambdaTest1() {
  var s := {3, 5, 7};
  var result := LambdaTest(s);
  assert result == true;
}

method TestLambdaTest2() {
  var s := {1, 2, 4};
  var result := LambdaTest(s);
  assert result == false;
}

method TestViaMapComprehension1() {
  var s := {5, 8, 12};
  var result := ViaMapComprehension(s);
  assert result == true;
}

method TestViaMapComprehension2() {
  var s := {1, 3, 7};
  var result := ViaMapComprehension(s);
  assert result == false;
}

method TestContains51() {
  var s := {2, 5, 8};
  var result := Contains5(s);
  assert result == true;
}

method TestContains52() {
  var s := {1, 3, 9};
  var result := Contains5(s);
  assert result == false;
}

method TestRIs51() {
  var r := MakeR(5);
  var result := RIs5(r);
  assert result == true;
}

method TestRIs52() {
  var r := MakeR(3);
  var result := RIs5(r);
  assert result == false;
}
