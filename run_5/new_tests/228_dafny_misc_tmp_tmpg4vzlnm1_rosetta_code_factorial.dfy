function Factorial(n: nat): nat {}

method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
{}

////////TESTS////////

method TestIterativeFactorial1() {
  var result := IterativeFactorial(5);
  assert result == 120;
}

method TestIterativeFactorial2() {
  var result := IterativeFactorial(0);
  assert result == 1;
}
