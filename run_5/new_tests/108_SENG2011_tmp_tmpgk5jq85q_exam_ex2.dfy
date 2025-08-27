method Getmini(a:array<int>) returns(mini:nat) 
requires a.Length > 0
ensures 0 <= mini < a.Length
ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x]
ensures forall x :: 0 <= x < mini ==> a[mini] < a[x]
{}

////////TESTS////////

method TestGetmini1() {
  var a := new int[4];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  a[3] := 1;
  var mini := Getmini(a);
  assert mini == 3;
}

method TestGetmini2() {
  var a := new int[3];
  a[0] := 10;
  a[1] := 10;
  a[2] := 15;
  var mini := Getmini(a);
  assert mini == 0;
}
