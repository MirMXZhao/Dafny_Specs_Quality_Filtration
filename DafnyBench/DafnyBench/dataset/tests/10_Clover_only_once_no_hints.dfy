method only_once<T(==)>(a: array<T>, key: T) returns (b:bool)
  ensures (multiset(a[..])[key] ==1 ) <==> b
{}

////////TESTS////////

method testonly_once1() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 2;
  var b := only_once(a, 1);
  assert b == true;
}

method testonly_once2() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 2;
  var b := only_once(a, 2);
  assert b == false;
}

method testonly_once3() {
  var a := new int[3];
  a[0] := 5;
  a[1] := 5;
  a[2] := 5;
  var b := only_once(a, 4);
  assert b == false;
}
