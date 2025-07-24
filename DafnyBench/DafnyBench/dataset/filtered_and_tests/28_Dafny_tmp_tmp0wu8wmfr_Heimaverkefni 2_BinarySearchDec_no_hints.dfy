// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/CGB1z

// Authors of solution:   Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/VnB5

// Use the command
//   dafny H2-skeleton.dfy
// or
//   compile H2-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;

{}

method SearchLoop( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j;
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
{}

// Ef eftirfarandi fall er ekki samþykkt þá eru
// föllin ekki að haga sér rétt að mati Dafny.
method Test( a: seq<real>, x: real )
    requires forall p,q | 0 <= p < q < |a| :: a[p] >= a[q];
{}


method TestSearchRecursive1() {
  var a := [10.0, 8.0, 6.0, 4.0, 2.0];
  var k := SearchRecursive(a, 0, 5, 5.0);
  assert k == 3;
}

method TestSearchRecursive2() {
  var a := [15.0, 10.0, 5.0];
  var k := SearchRecursive(a, 1, 3, 7.0);
  assert k == 2;
}

method TestSearchLoop1() {
  var a := [10.0, 8.0, 6.0, 4.0, 2.0];
  var k := SearchLoop(a, 0, 5, 5.0);
  assert k == 3;
}

method TestSearchLoop2() {
  var a := [15.0, 10.0, 5.0];
  var k := SearchLoop(a, 1, 3, 7.0);
  assert k == 2;
}

method TestTest1() {
  var a := [10.0, 8.0, 6.0, 4.0, 2.0];
  Test(a, 5.0);
}

method TestTest2() {
  var a := [1.0];
  Test(a, 0.5);
}
