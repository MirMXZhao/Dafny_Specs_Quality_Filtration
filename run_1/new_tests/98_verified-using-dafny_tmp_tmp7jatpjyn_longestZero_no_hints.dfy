function getSize(i: int, j:int) : int
{
    j - i + 1    
}

method longestZero(a: array<int>) returns (sz:int, pos:int)   
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i:int  :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{}

////////TESTS////////

method TestLongestZero1() {
  var a := new int[5];
  a[0] := 1; a[1] := 0; a[2] := 0; a[3] := 0; a[4] := 1;
  var sz, pos := longestZero(a);
  assert sz == 3;
  assert pos == 1;
}

method TestLongestZero2() {
  var a := new int[4];
  a[0] := 0; a[1] := 1; a[2] := 0; a[3] := 2;
  var sz, pos := longestZero(a);
  assert sz == 1;
  assert pos == 0;
}
