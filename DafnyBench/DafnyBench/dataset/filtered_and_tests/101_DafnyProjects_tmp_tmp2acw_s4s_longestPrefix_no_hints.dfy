// MFES, Exam 8/Sept/20201, Exercise 5 

// Computes the length (i) of the longest common prefix (initial subarray) 
// of two arrays a and b. 
method longestPrefix(a: array<int>, b: array <int>) returns (i: nat) 
 ensures i <= a.Length && i <= b.Length
 ensures a[..i] == b[..i]
 ensures i < a.Length && i < b.Length ==> a[i] != b[i]
{}
 
// Test method with an example.
method testLongestPrefix() {}



method testLongestPrefix1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var b := new int[4];
  b[0] := 1; b[1] := 2; b[2] := 5; b[3] := 6;
  var i := longestPrefix(a, b);
  assert i == 2;
}

method testLongestPrefix2() {
  var a := new int[3];
  a[0] := 7; a[1] := 8; a[2] := 9;
  var b := new int[3];
  b[0] := 7; b[1] := 8; b[2] := 9;
  var i := longestPrefix(a, b);
  assert i == 3;
}
