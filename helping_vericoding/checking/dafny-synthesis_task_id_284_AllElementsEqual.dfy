method AllElementsEqual(a: array<int>, n: int) returns (result: bool)
  ensures result ==> forall i :: 0 <= i < a.Length ==> a[i] == n
  ensures !result ==> exists i :: 0 <= i < a.Length && a[i] != n
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == n
  {
    if a[i] != n {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}

method Main()
{
    var a := new int [3] [-3, -3, -3];
    var b:= new int [2][2, 1];
    var c:= new int [5] [1, 1, 1, 1, 5];
    var a1 := AllElementsEqual(a, -3);
    var a1' := AllElementsEqual(a, 4);
    var b1 := AllElementsEqual(b, 1);
    var b1' := AllElementsEqual(b, 3);
    var c1 := AllElementsEqual(c, 1);
}