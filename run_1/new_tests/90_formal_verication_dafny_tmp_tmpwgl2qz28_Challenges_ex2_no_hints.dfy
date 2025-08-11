method Forbid42(x:int, y:int) returns (z:int)
requires y != 42;
ensures z == x/(42-y);
{} 

method Allow42(x:int, y:int) returns (z: int, err:bool) 
ensures y != 42 ==> z == x/(42-y) && err == false;
ensures y == 42 ==> z == 0 && err == true;
{}

////////TESTS////////

method TestForbid421() {
  var z := Forbid42(84, 0);
  assert z == 2;
}

method TestForbid422() {
  var z := Forbid42(126, 21);
  assert z == 6;
}

method TestAllow421() {
  var z, err := Allow42(84, 0);
  assert z == 2;
  assert err == false;
}

method TestAllow422() {
  var z, err := Allow42(100, 42);
  assert z == 0;
  assert err == true;
}
