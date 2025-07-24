function pow(base: int, exponent: int): int
  requires exponent >= 0
{}

method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
  requires operators != [] && operands != [] && |operators| + 1 == |operands|
  requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
{}

