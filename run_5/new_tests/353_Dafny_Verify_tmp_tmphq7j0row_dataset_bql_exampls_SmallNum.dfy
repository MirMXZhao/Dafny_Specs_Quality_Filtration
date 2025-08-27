method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
	requires n > 0;
    requires n <= a.Length;
	requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
	ensures r <= max * n;
{}

////////TESTS////////

method Testadd_small_numbers1() {
  var a := new int[3];
  a[0] := 2;
  a[1] := 3;
  a[2] := 1;
  var r := add_small_numbers(a, 3, 5);
  assert r <= 15;
}

method Testadd_small_numbers2() {
  var a := new int[4];
  a[0] := 1;
  a[1] := 0;
  a[2] := 2;
  a[3] := 4;
  var r := add_small_numbers(a, 2, 3);
  assert r <= 6;
}
