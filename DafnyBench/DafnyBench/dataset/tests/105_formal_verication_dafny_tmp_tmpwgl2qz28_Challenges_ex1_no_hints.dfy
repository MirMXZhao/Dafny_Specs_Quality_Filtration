method PalVerify(a: array<char>) returns (yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j]) 
{}

////////TESTS////////

method TestPalVerify1() {
  var a := new char[5];
  a[0] := 'r';
  a[1] := 'a';
  a[2] := 'c';
  a[3] := 'e';
  a[4] := 'c';
  var yn := PalVerify(a);
  assert yn == false;
}

method TestPalVerify2() {
  var a := new char[5];
  a[0] := 'r';
  a[1] := 'a';
  a[2] := 'c';
  a[3] := 'a';
  a[4] := 'r';
  var yn := PalVerify(a);
  assert yn == true;
}

method TestPalVerify3() {
  var a := new char[0];
  var yn := PalVerify(a);
  assert yn == true;
}
