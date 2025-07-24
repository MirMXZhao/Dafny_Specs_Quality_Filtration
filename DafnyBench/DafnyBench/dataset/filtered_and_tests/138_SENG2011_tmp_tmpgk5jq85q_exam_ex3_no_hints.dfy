method Symmetric(a: array<int>) returns (flag: bool)
ensures flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1]
ensures flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1]
{}
/*
method Main() {}
*/


method TestSymmetric1() {
  var a := new int[5];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 2; a[4] := 1;
  var flag := Symmetric(a);
  assert flag == true;
}

method TestSymmetric2() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 1;
  var flag := Symmetric(a);
  assert flag == false;
}
