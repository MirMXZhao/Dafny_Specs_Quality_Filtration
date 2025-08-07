method Getmini(a:array<int>) returns(mini:nat) 
requires a.Length > 0
ensures 0 <= mini < a.Length
ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x]
ensures forall x :: 0 <= x < mini ==> a[mini] < a[x]
{}

////////TESTS////////

method TestGetmini1() {
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 3, 1, 4, 2;
  var mini := Getmini(a);
  assert mini == 1;
}

method TestGetmini2() {
  var a := new int[3];
  a[0], a[1], a[2] := 5, 7, 5;
  var mini := Getmini(a);
  assert mini == 0;
}

method TestGetmini3() {
  var a := new int[1];
  a[0] := 42;
  var mini := Getmini(a);
  assert mini == 0;
}
