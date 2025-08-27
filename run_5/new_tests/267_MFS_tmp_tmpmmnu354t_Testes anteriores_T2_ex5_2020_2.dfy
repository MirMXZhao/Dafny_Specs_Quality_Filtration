method leq(a: array<int>, b: array<int>) returns (result: bool) 
    ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{}

////////TESTS////////

method TestLeq1() {
  var a := new int[3] [1, 2, 3];
  var b := new int[4] [1, 2, 3, 4];
  var result := leq(a, b);
  assert result == true;
}

method TestLeq2() {
  var a := new int[3] [1, 3, 2];
  var b := new int[3] [1, 2, 4];
  var result := leq(a, b);
  assert result == true;
}
