newtype uint32 = i:int | 0 <= i < 0x100000000

method returnANullArray() returns (a: array?<uint32>)
  ensures a == null
{
  a := null;
}

method returnANonNullArray() returns (a: array?<uint32>)
  ensures a != null
  ensures a.Length == 5
{}

method LinearSearch(a: array<uint32>, len:uint32, key: uint32) returns (n: uint32)
  requires a.Length == len as int
  ensures 0 <= n <= len
  ensures n == len || a[n] == key
{}

method PrintArray<A>(a:array?<A>, len:uint32)
  requires a != null ==> len as int == a.Length
{}

datatype ArrayDatatype = AD(ar: array<uint32>)

////////TESTS////////

method TestReturnANullArray1() {
  var a := returnANullArray();
  assert a == null;
}

method TestReturnANullArray2() {
  var a := returnANullArray();
  assert a == null;
}

method TestReturnANonNullArray1() {
  var a := returnANonNullArray();
  assert a != null;
  assert a.Length == 5;
}

method TestReturnANonNullArray2() {
  var a := returnANonNullArray();
  assert a != null;
  assert a.Length == 5;
}

method TestLinearSearch1() {
  var a := new uint32[3];
  a[0] := 10; a[1] := 20; a[2] := 30;
  var n := LinearSearch(a, 3, 20);
  assert 0 <= n <= 3;
  assert n == 3 || a[n] == 20;
}

method TestLinearSearch2() {
  var a := new uint32[2];
  a[0] := 5; a[1] := 15;
  var n := LinearSearch(a, 2, 25);
  assert 0 <= n <= 2;
  assert n == 2 || a[n] == 25;
}
