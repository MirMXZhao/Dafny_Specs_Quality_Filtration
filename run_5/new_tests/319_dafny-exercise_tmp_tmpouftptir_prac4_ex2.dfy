predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{}

////////TESTS////////

method TestGetTriple1() {
  var a := new int[5];
  a[0] := 1; a[1] := 2; a[2] := 2; a[3] := 2; a[4] := 3;
  var index := GetTriple(a);
  assert index == 1;
}

method TestGetTriple2() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 4;
  var index := GetTriple(a);
  assert index == 4;
}
