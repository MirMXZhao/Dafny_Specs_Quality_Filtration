function getSize(i: int, j:int) : int
{
    j - i + 1    
}

// For a given integer array, let's find the longest subesquence of 0s.
// sz: size, pos: position.   a[pos..(pos+sz)] will be all zeros
method longestZero(a: array<int>) returns (sz:int, pos:int)   
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i:int  :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{}



method Main()
{}





method TestLongestZero1() {
  var a := new int[7];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6] := 1, 0, 0, 0, 1, 0, 2;
  var sz, pos := longestZero(a);
  assert sz == 3;
  assert pos == 1;
}

method TestLongestZero2() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 2, 1, 4, 5;
  var sz, pos := longestZero(a);
  assert sz == 0;
  assert pos == 0;
}
