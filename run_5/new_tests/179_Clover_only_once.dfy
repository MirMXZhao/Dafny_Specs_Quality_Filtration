method only_once<T(==)>(a: array<T>, key: T) returns (b:bool)
  ensures (multiset(a[..])[key] ==1 ) <==> b
{}

////////TESTS////////

method Testonly_once1() {
  var a := new int[4];
  a[0] := 1; a[1] := 2; a[2] := 3; a[3] := 2;
  var b := only_once(a, 2);
  assert b == false;
}

method Testonly_once2() {
  var a := new int[3];
  a[0] := 5; a[1] := 7; a[2] := 9;
  var b := only_once(a, 7);
  assert b == true;
}
