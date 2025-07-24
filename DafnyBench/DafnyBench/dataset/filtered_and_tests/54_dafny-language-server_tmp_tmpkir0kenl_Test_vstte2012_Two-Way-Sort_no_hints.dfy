// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This method is a slight generalization of the
// code provided in the problem statement since it
// is generic in the type of the array elements.
method swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
{}

// This method is a direct translation of the pseudo
// code given in the problem statement.
// The first postcondition expresses that the resulting
// array is sorted, that is, all occurrences of "false"
// come before all occurrences of "true".
// The second postcondition expresses that the post-state
// array is a permutation of the pre-state array. To express
// this, we use Dafny's built-in multisets. The built-in
// function "multiset" takes an array and yields the
// multiset of the array elements.
// Note that Dafny guesses a suitable ranking function
// for the termination proof of the while loop.
// We use the loop guard from the given pseudo-code.  However,
// the program also verifies with the stronger guard "i < j"
// (without changing any of the other specifications or
// annotations).
method two_way_sort(a: array<bool>)
  modifies a
  ensures forall m,n :: 0 <= m < n < a.Length ==> (!a[m] || a[n])
  ensures multiset(a[..]) == old(multiset(a[..]))
{}



method TestSwap1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 10, 20, 30, 40;
  swap(a, 1, 2);
  assert a[0] == 10;
  assert a[1] == 30;
  assert a[2] == 20;
  assert a[3] == 40;
}

method TestSwap2() {
  var a := new string[3];
  a[0], a[1], a[2] := "hello", "world", "test";
  swap(a, 0, 2);
  assert a[0] == "test";
  assert a[1] == "world";
  assert a[2] == "hello";
}

method TestTwoWaySort1() {
  var a := new bool[5];
  a[0], a[1], a[2], a[3], a[4] := true, false, true, false, false;
  two_way_sort(a);
  assert a[0] == false;
  assert a[1] == false;
  assert a[2] == false;
  assert a[3] == true;
  assert a[4] == true;
}

method TestTwoWaySort2() {
  var a := new bool[3];
  a[0], a[1], a[2] := false, false, true;
  two_way_sort(a);
  assert a[0] == false;
  assert a[1] == false;
  assert a[2] == true;
}
