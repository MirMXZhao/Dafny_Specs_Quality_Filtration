function countTo( a:array<bool>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{}

method CountTrue(a: array<bool>) returns (result: int)
    requires a != null
    ensures result == countTo(a, a.Length)
{}

////////TESTS////////

method TestCountTrue1() {
  var a := new bool[4];
  a[0] := true;
  a[1] := false;
  a[2] := true;
  a[3] := true;
  var result := CountTrue(a);
  assert result == countTo(a, a.Length);
}

method TestCountTrue2() {
  var a := new bool[3];
  a[0] := false;
  a[1] := false;
  a[2] := false;
  var result := CountTrue(a);
  assert result == countTo(a, a.Length);
}
