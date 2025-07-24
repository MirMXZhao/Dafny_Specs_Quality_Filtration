method only_once<T(==)>(a: array<T>, key: T) returns (b:bool)
  ensures (multiset(a[..])[key] ==1 ) <==> b
{}


method TestOnlyOnce1() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 2;
  var b := only_once(a, 1);
  assert b == true;
}

method TestOnlyOnce2() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 2;
  var b := only_once(a, 2);
  assert b == false;
}
