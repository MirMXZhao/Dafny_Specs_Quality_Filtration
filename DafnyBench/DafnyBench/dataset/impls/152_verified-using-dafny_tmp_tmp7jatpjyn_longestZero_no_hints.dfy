method longestZero(a: array<int>) returns (sz:int, pos:int)   
    requires 1 <= a.Length
    ensures 0 <= sz <= a.Length
    ensures 0 <= pos < a.Length
    ensures pos + sz <= a.Length
    ensures forall i:int  :: pos <= i < pos + sz ==> a[i] == 0
    ensures forall i,j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
    sz := 0;
    pos := 0;
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= sz <= a.Length
        invariant 0 <= pos < a.Length
        invariant pos + sz <= a.Length
        invariant forall k :: pos <= k < pos + sz ==> a[k] == 0
        invariant forall start, end :: (0 <= start < end < i && getSize(start, end) > sz) ==> exists k :: start <= k <= end && a[k] != 0
    {
        if a[i] == 0 {
            var start := i;
            var count := 0;
            while i < a.Length && a[i] == 0
                invariant start <= i <= a.Length
                invariant count == i - start
                invariant forall k :: start <= k < i ==> a[k] == 0
            {
                count := count + 1;
                i := i + 1;
            }
            if count > sz {
                sz := count;
                pos := start;
            }
        } else {
            i := i + 1;
        }
    }
}

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