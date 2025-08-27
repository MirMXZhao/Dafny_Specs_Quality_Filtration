ghost predicate prime(n: nat)
{ n > 1 && (forall nr | 1 < nr < n :: n % nr != 0) }

datatype Answer = Yes | No | Unknown

class {:autocontracts} PrimeMap{

  var database: map<nat, bool>; 

  ghost predicate Valid()
    reads this
  {
    forall i | i in database.Keys :: (database[i] == true <==> prime(i)) 
  }

  constructor()
    ensures database == map[]
  {}

  method InsertPrime(n: nat)
    modifies this;
    ensures database.Keys == old(database.Keys) + {n}
    requires prime(n)
    ensures database == database[n := true] 
  {}

  method InsertNumber(n: nat) 
    modifies this
    ensures database.Keys == old(database.Keys) + {n}
    ensures prime(n) <==> database == database[n := true] 
    ensures !prime(n) <==> database == database[n := false] 
  {}

  method IsPrime?(n: nat) returns (answer: Answer) 
      ensures database.Keys == old(database.Keys)
      ensures (n in database) && prime(n) <==> answer == Yes 
      ensures (n in database) && !prime(n) <==> answer == No 
      ensures !(n in database) <==> answer == Unknown
  {}

  method testPrimeness(n: nat) returns (result: bool) 
      requires n >= 0
      ensures result <==> prime(n)
  {}
}

////////TESTS////////

method TestIsPrime1() {
  var pm := new PrimeMap();
  pm.InsertPrime(7);
  var answer := pm.IsPrime?(7);
  assert answer == Yes;
}

method TestIsPrime2() {
  var pm := new PrimeMap();
  pm.InsertNumber(4);
  var answer := pm.IsPrime?(4);
  assert answer == No;
}

method TestTestPrimeness1() {
  var pm := new PrimeMap();
  var result := pm.testPrimeness(7);
  assert result == true;
}

method TestTestPrimeness2() {
  var pm := new PrimeMap();
  var result := pm.testPrimeness(4);
  assert result == false;
}
