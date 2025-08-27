class Secret{
    var secret : int;
    var known : bool;
    var count : int;

    method Init(x : int)
    modifies `secret, `known, `count
    requires 1 <= x <= 10
    ensures secret == x
    ensures known == false
    ensures count == 0
    {}

    method Guess(g : int) returns (result : bool, guesses : int)
    modifies `known, `count
    requires known == false
    ensures if g == secret then 
                result == true && known == true 
            else 
                result == false && known == false
    ensures count == old(count) + 1 && guesses == count
    {}
}

////////TESTS////////

method TestGuess1() {
  var s := new Secret;
  s.Init(5);
  var result, guesses := s.Guess(5);
  assert result == true;
  assert guesses == 1;
}

method TestGuess2() {
  var s := new Secret;
  s.Init(7);
  var result, guesses := s.Guess(3);
  assert result == false;
  assert guesses == 1;
}
