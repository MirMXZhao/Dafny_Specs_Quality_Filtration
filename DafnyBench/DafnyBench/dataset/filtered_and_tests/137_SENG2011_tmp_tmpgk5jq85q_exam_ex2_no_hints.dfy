method Getmini(a:array<int>) returns(mini:nat) 
requires a.Length > 0
ensures 0 <= mini < a.Length // mini is an index of a
ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x] // a[mini] is the minimum value
ensures forall x :: 0 <= x < mini ==> a[mini] < a[x] // a[mini] is the first min
{}

/*
method check() {}
*/



method TestGetmini1() {
  var a := new int[4];
  a[0] := 3;
  a[1] := 1;
  a[2] := 4;
  a[3] := 1;
  var mini := Getmini(a);
  assert mini == 1;
}

method TestGetmini2() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 2;
  a[2] := 8;
  var mini := Getmini(a);
  assert mini == 1;
}
